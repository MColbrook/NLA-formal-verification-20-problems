"""Trust-boundary regressions for the opt-in compiled proof cache importer."""
import base64
import io
import json
import tarfile
import tempfile
import unittest
from pathlib import Path

from parallel_build import inventory
from verified_combined_cache import COMMIT, ENDINGS, canonical, load_verified_cache, sha


class VerifiedCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.version = 'Lean (version 4.35.0, native, commit ' + COMMIT + ', Release)'
        self.compiler = {'sha256': 'linux-compiler', 'version': self.version, 'path': '/old/lean'}
        self.external_path = self.root / 'external.olean'
        self.external_path.write_bytes(b'pinned-external')
        self.nodes = {}
        artifacts = {}
        for module, imports, outside in [('B', [], ['Mathlib']), ('A', ['B'], []),
                                         ('Solution', ['A'], []), ('Challenge', [], ['Mathlib'])]:
            source = self.root / (module + '.lean')
            source.write_text('import ' + ' '.join(imports + outside) + '\n', encoding='utf-8')
            self.nodes[module] = {'source': source, 'sha256': sha(source.read_bytes()),
                                  'imports': imports, 'external': {name: self.external(name) for name in outside}}
            stem = self.root / '.lake/build/lib/lean' / module
            stem.parent.mkdir(parents=True, exist_ok=True)
            artifacts[module] = []
            for ending in ENDINGS:
                path = Path(str(stem) + ending)
                path.write_bytes((module + ending).encode())
                artifacts[module].append({'path': str(path), 'sha256': sha(path.read_bytes())})
        self.origin = {'compiler': self.compiler, 'records': []}
        self.manifest = {'compiler_origin': self.compiler, 'native_format_probe_passed': True, 'modules': []}
        signatures = {}
        for module in ['B', 'A']:
            node = self.nodes[module]
            binding = {'source_sha256': node['sha256'], 'compiler_sha256': self.compiler['sha256'],
                       'module': module, 'imports': {'ID::' + name: signatures[name] for name in node['imports']},
                       'external_imports': {name: {'sha256': data['sha256']} for name, data in node['external'].items()}}
            signatures[module] = canonical(binding)
            archived_artifacts = [{'path': '/old/lib/lean/' + module + ending, 'sha256': item['sha256']}
                                  for ending, item in zip(ENDINGS, artifacts[module])]
            self.origin['records'].append({'id': 'ID', 'module': module, 'binding': binding,
                'signature': signatures[module], 'source_sha256': node['sha256'], 'status': 'pass',
                'exit_code': 0, 'source_stable': True, 'artifacts': archived_artifacts})
            self.manifest['modules'].append({'module': module, 'original_id': 'ID',
                'original_signature': signatures[module], 'source_sha256': node['sha256'], 'artifacts': artifacts[module]})
        self.native = {'compiler_sha256': 'native-compiler', 'compiler_version': self.version,
                       'modules': [{'module': 'Solution', 'source_sha256': self.nodes['Solution']['sha256'],
                                    'source_stable': True, 'status': 'pass', 'exit_code': 0,
                                    'artifacts': artifacts['Solution']}]}
        rows, digest = inventory(self.root)
        self.prior_row = {'source_inventory_sha256': digest, 'compiler_sha256': 'native-compiler',
                          'compiler_version': self.version, 'source_stable': True, 'exit_code': 0,
                          'combined_solution_compiled': True, 'verified_component_cache_origin_compiler': self.compiler,
                          'native_format_probe_passed': True, 'solution_artifacts': artifacts['Solution']}
        self.snapshot = {'source_inventory': rows, 'source_inventory_sha256': digest}
        self.write_bindings()

    def external(self, name):
        return {'path': str(self.external_path), 'sha256': sha(self.external_path.read_bytes())}

    def write_bindings(self):
        cache = self.root / '.lake'
        record_bytes = json.dumps(self.origin).encode()
        with tarfile.open(cache / 'origin.tar.gz', 'w:gz') as archive:
            member = tarfile.TarInfo('module-results.json')
            member.size = len(record_bytes)
            archive.addfile(member, io.BytesIO(record_bytes))
        self.manifest['original_module_results_sha256'] = sha(record_bytes)
        self.prior_row['verified_component_cache_original_receipt_sha256'] = sha(record_bytes)
        prior_bytes = json.dumps({'status': 'pass', 'projects': [self.prior_row]}).encode()
        prior_path = self.root / 'verification/combined-build-status.json'
        prior_path.parent.mkdir(parents=True, exist_ok=True)
        prior_path.write_bytes(prior_bytes)
        self.snapshot['combined_receipt_sha256'] = sha(prior_bytes)
        self.snapshot['combined_receipt_base64'] = base64.b64encode(prior_bytes).decode()
        for name, value in [('manifest.json', self.manifest), ('native.json', self.native), ('inventory.json', self.snapshot)]:
            (cache / name).write_text(json.dumps(value), encoding='utf-8')

    def load(self, **overrides):
        args = dict(root=self.root, manifest_path=self.root / '.lake/manifest.json',
                    archive_path=self.root / '.lake/origin.tar.gz', native_path=self.root / '.lake/native.json',
                    inventory_path=self.root / '.lake/inventory.json', compiler_sha='native-compiler',
                    compiler_version=self.version, nodes=self.nodes, external=self.external)
        args.update(overrides)
        return load_verified_cache(**args)

    def test_valid_cache_allows_only_new_challenge(self):
        (self.root / 'Challenge.lean').write_text('new challenge\n', encoding='utf-8')
        rows, report = self.load()
        self.assertEqual(set(rows), {'A', 'B', 'Solution'})
        self.assertEqual(report['pinned_external_imports_validated'], 1)

    def test_changed_source_is_rejected(self):
        (self.root / 'A.lean').write_text('changed\n', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'source input'):
            self.load()

    def test_tampered_artifact_is_rejected(self):
        Path(self.manifest['modules'][0]['artifacts'][0]['path']).write_bytes(b'tampered')
        with self.assertRaisesRegex(ValueError, 'artifact bytes'):
            self.load()

    def test_duplicate_artifact_record_is_rejected(self):
        rows = self.manifest['modules'][0]['artifacts']
        rows[0] = dict(rows[1])
        self.write_bindings()
        with self.assertRaisesRegex(ValueError, 'artifact'):
            self.load()

    def test_later_failed_build_cannot_erase_preserved_origin(self):
        (self.root / 'verification/combined-build-status.json').write_text('{"status":"fail"}', encoding='utf-8')
        rows, _ = self.load()
        self.assertEqual(set(rows), {'A', 'B', 'Solution'})

    def test_changed_pinned_external_is_rejected(self):
        self.external_path.write_bytes(b'changed-external')
        with self.assertRaisesRegex(ValueError, 'pinned external artifact'):
            self.load()

    def test_stale_import_binding_is_rejected_even_when_resigned(self):
        row = self.origin['records'][1]
        row['binding']['imports']['ID::B'] = 'stale-signature'
        row['signature'] = canonical(row['binding'])
        self.manifest['modules'][1]['original_signature'] = row['signature']
        self.write_bindings()
        with self.assertRaisesRegex(ValueError, 'import signature'):
            self.load()

    def test_changed_consumer_compiler_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'native compiler binding'):
            self.load(compiler_sha='different-native-compiler')

    def test_changed_archived_compiler_is_rejected(self):
        self.compiler['version'] = 'wrong compiler'
        self.write_bindings()
        with self.assertRaisesRegex(ValueError, 'archived compiler version'):
            self.load()


if __name__ == '__main__':
    unittest.main()
