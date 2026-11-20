"""Validate an opt-in, previously compiled cache before the ordinary root build.

The archived compiler bindings certify portable component artifacts. The native
receipt and its complete old inventory certify local interface artifacts. Only
Challenge.lean may differ from that inventory, and it is never imported here.
"""
from __future__ import annotations

import hashlib
import base64
import json
import tarfile
from pathlib import Path

from parallel_build import inventory

COMMIT = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
ENDINGS = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return sha(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def require(condition, message):
    if not condition:
        raise ValueError('Verified cache rejected: ' + message)


def artifact_hashes(rows, module):
    """Require exactly one authoritative artifact for each module suffix."""
    stem = module.replace('.', '/')
    result = {}
    require(len(rows) == len(ENDINGS), module + ': incomplete artifact set')
    for row in rows:
        name = row['path'].replace('\\', '/')
        matches = [ending for ending in ENDINGS if name.endswith('/' + stem + ending)]
        require(len(matches) == 1, module + ': unexpected artifact path')
        ending = matches[0]
        require(ending not in result, module + ': duplicate artifact')
        result[ending] = row['sha256']
    require(set(result) == set(ENDINGS), module + ': incomplete artifact suffixes')
    return result


def local_artifacts(root, module, rows):
    stem = root / '.lake/build/lib/lean' / Path(*module.split('.'))
    expected = {str(Path(str(stem) + ending)) for ending in ENDINGS}
    require(len(rows) == len(ENDINGS) and {row['path'] for row in rows} == expected,
            module + ': local artifact paths differ from expected five')
    for row in rows:
        path = Path(row['path'])
        require(path.is_file() and not path.is_symlink(), module + ': missing local artifact')
        require(sha(path.read_bytes()) == row['sha256'], module + ': local artifact bytes changed')
    return artifact_hashes(rows, module)


def load_verified_cache(*, root, manifest_path, archive_path, native_path,
                        inventory_path, compiler_sha, compiler_version, nodes, external):
    """Return validated candidates; never write stamps or declare a fresh build."""
    root = Path(root).resolve()
    manifest_bytes = Path(manifest_path).read_bytes()
    manifest = json.loads(manifest_bytes)
    native_bytes = Path(native_path).read_bytes()
    native = json.loads(native_bytes)
    old_inventory = json.loads(Path(inventory_path).read_bytes())
    prior_bytes = base64.b64decode(old_inventory['combined_receipt_base64'], validate=True)
    prior = json.loads(prior_bytes)
    require(prior.get('status') == 'pass' and len(prior.get('projects', [])) == 1,
            'missing successful prior combined receipt')
    prior_row = prior['projects'][0]
    require(old_inventory['combined_receipt_sha256'] == sha(prior_bytes), 'prior receipt changed')
    old_rows = old_inventory['source_inventory']
    old_digest = canonical(old_rows)
    require(old_digest == old_inventory['source_inventory_sha256'] == prior_row['source_inventory_sha256'],
            'old source inventory is not bound to the prior successful build')
    current_rows, _ = inventory(root)
    unchanged = lambda rows: [row for row in rows if row['path'] != 'Challenge.lean']
    require(unchanged(old_rows) == unchanged(current_rows), 'source input other than Challenge changed')
    require('version 4.35.0,' in compiler_version and 'commit ' + COMMIT in compiler_version,
            'consumer compiler version differs')
    require(native['compiler_version'] == compiler_version and native['compiler_sha256'] == compiler_sha,
            'native compiler binding differs')
    require(prior_row['compiler_version'] == compiler_version and prior_row['compiler_sha256'] == compiler_sha,
            'prior combined compiler differs')
    require(prior_row.get('source_stable') is True and prior_row.get('exit_code') == 0
            and prior_row.get('combined_solution_compiled') is True, 'prior combined build was incomplete')

    with tarfile.open(archive_path, 'r:gz') as archive:
        members = [member for member in archive.getmembers() if member.name == 'module-results.json']
        require(len(members) == 1 and members[0].isfile(), 'ambiguous archive receipt')
        record_bytes = archive.extractfile(members[0]).read()
    require(sha(record_bytes) == manifest['original_module_results_sha256']
            == prior_row['verified_component_cache_original_receipt_sha256'], 'archive receipt hash differs')
    origin = json.loads(record_bytes)
    compiler = origin['compiler']
    require(compiler == manifest['compiler_origin'] == prior_row['verified_component_cache_origin_compiler'],
            'archived compiler provenance differs')
    require('version 4.35.0,' in compiler['version'] and 'commit ' + COMMIT in compiler['version'],
            'archived compiler version differs')
    require(manifest.get('native_format_probe_passed') is True and prior_row.get('native_format_probe_passed') is True,
            'portable artifact format was not tested natively')
    records = {}
    for row in origin['records']:
        key = (row['id'], row['module'])
        require(key not in records, 'duplicate archived module')
        records[key] = row
    component_rows = manifest['modules']
    components = {row['module']: row for row in component_rows}
    require(len(components) == len(component_rows), 'duplicate component cache module')
    native_rows = native['modules']
    native_modules = {row['module']: row for row in native_rows}
    require(len(native_modules) == len(native_rows) and not (set(components) & set(native_modules)),
            'duplicate native cache module')
    require('Solution' in native_modules and 'Challenge' not in native_modules,
            'native cache must contain Solution and exclude Challenge')
    checked_records = set()
    checked_externals = set()
    external_hashes = {}

    def validate_archived(key):
        if key in checked_records:
            return
        require(key in records, 'missing archived import ' + str(key))
        row = records[key]
        module = row['module']
        binding = row['binding']
        require(row.get('status') == 'pass' and row.get('exit_code') == 0 and row.get('source_stable') is True,
                module + ': archived compilation did not pass')
        require(binding.get('compiler_sha256') == compiler['sha256'] and binding.get('module') == module,
                module + ': archived compiler/module binding differs')
        require(row['signature'] == canonical(binding), module + ': archived signature differs')
        require(module in components and module in nodes, module + ': archived dependency is not in current closure')
        cached = components[module]
        require(row['source_sha256'] == binding['source_sha256'] == cached['source_sha256'] == nodes[module]['sha256'],
                module + ': archived source bytes differ')
        require(artifact_hashes(row['artifacts'], module) == artifact_hashes(cached['artifacts'], module),
                module + ': archived dependency artifacts differ')
        imported = {}
        for name, signature in binding['imports'].items():
            owner, dependency = name.split('::', 1)
            require(owner == row['id'] and dependency not in imported, module + ': invalid archived import key')
            require((owner, dependency) in records and records[(owner, dependency)]['signature'] == signature,
                    module + ': archived import signature differs')
            imported[dependency] = (owner, dependency)
        require(set(imported) == set(nodes[module]['imports']), module + ': local import graph differs')
        require(set(binding['external_imports']) == set(nodes[module]['external']), module + ': external import graph differs')
        for name, record in binding['external_imports'].items():
            current = external(name)
            require(current['sha256'] == record['sha256'], module + ': pinned external artifact differs: ' + name)
            checked_externals.add(name)
            require(name not in external_hashes or external_hashes[name] == record['sha256'],
                    'conflicting archived external binding: ' + name)
            external_hashes[name] = record['sha256']
        # Mark before descending, but a current source cycle is rejected by the ordinary builder.
        checked_records.add(key)
        for dependency in imported.values():
            validate_archived(dependency)

    result = {}
    common = {'kind': 'validated-prior-source-compilation', 'archive_receipt_sha256': sha(record_bytes),
              'cache_manifest_sha256': sha(manifest_bytes), 'prior_native_receipt_sha256': sha(native_bytes),
              'prior_combined_receipt_sha256': sha(prior_bytes), 'prior_source_inventory_sha256': old_digest,
              'consumer_compiler_sha256': compiler_sha, 'native_format_probe_passed': True}
    for module in sorted(set(nodes) & set(components)):
        cached = components[module]
        require(cached['original_signature'] == records[(cached['original_id'], module)]['signature'],
                module + ': original cache signature differs')
        validate_archived((cached['original_id'], module))
        local_artifacts(root, module, cached['artifacts'])
        result[module] = {**cached, 'cache_import_provenance': {**common, 'source_compiler': compiler,
                          'original_id': cached['original_id'], 'original_signature': cached['original_signature']}}
    for module in sorted(set(nodes) & set(native_modules)):
        row = native_modules[module]
        require(row.get('status') == 'pass' and row.get('source_stable') is True and row.get('exit_code') == 0,
                module + ': native compilation did not pass')
        require(row['source_sha256'] == nodes[module]['sha256'], module + ': native source bytes differ')
        local_artifacts(root, module, row['artifacts'])
        require(all(name in result or name in native_modules for name in nodes[module]['imports']),
                module + ': unbound native import')
        for name, record in nodes[module]['external'].items():
            require(name in external_hashes and record['sha256'] == external_hashes[name],
                    module + ': native pinned external binding is unverified: ' + name)
        if module == 'Solution':
            require(artifact_hashes(row['artifacts'], module) == artifact_hashes(prior_row['solution_artifacts'], module),
                    'Solution artifacts differ from prior combined receipt')
        result[module] = {**row, 'cache_import_provenance': {**common, 'source_compiler': {
                          'sha256': compiler_sha, 'version': compiler_version}}}
    # A native root may only depend on validated cached artifacts and other such native roots.
    for module in set(result) & set(native_modules):
        require(all(name in result for name in nodes[module]['imports']), module + ': incomplete native dependency closure')
    require('Challenge' not in result, 'Challenge must be freshly compiled')
    return result, {'modules_validated': len(result), 'archived_bindings_validated': len(checked_records),
                    'pinned_external_imports_validated': len(checked_externals), **common,
                    'source_compiler': compiler}
