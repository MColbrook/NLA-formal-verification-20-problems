#!/usr/bin/env python3
"""Build explicit standalone Challenge surfaces from unchanged source statements.

The whole-closure mode is deliberately conservative: it preserves mathematical
commands and their source contexts and refuses oversized or unsupported entries.
No Lean elaboration, build, proof replay, or semantic equivalence is claimed.

  python scripts/build_entry_interfaces.py capture --source-root ../lean
  python scripts/build_entry_interfaces.py build --ids IS-03 MI-19 MI-21 MI-22
"""
from __future__ import annotations

import argparse
import gzip
import io
import json
from pathlib import Path
import re
import tarfile

from stage_sources import ROOT, load_json, write_json, sha256, source_mask, checked_path, read_archive

PRIMARY = ROOT / "primary-entry-targets.json"
STATEMENTS = ROOT / "archives" / "original-primary-entry-statements.tar.gz"
STATEMENT_MANIFEST = ROOT / "audit" / "entry-statement-inputs.json"
INTERFACES = ROOT / "audit" / "entry-interfaces.json"

# Reviewed module pruning: every semantic declaration used by IE-22 Definitions
# is already present in IE-21 Definitions; the other transitive imports establish
# estimates rather than define objects occurring in the selected theorem types.
REVIEWED_UNUSED_UTILITY_IMPORTS = {
    "MF-05": {"LeanCert.Tactic.Verification"},
    "PF-02": {"LeanCert.Tactic"},
}

REVIEWED_OMITTED_HELPER_MODULES = {
    # This module declares only placeholder helper theorems; all semantic
    # definitions are in its imported modules, retained in their original order.
    "PF-02": {"NLA.PF02.UniformPositiveOrientationChallenge"},
}

REVIEWED_MODULE_PRUNING = {
    "IE-22": ["NLA.IE21.Definitions", "NLA.IE22.Definitions", "NLA.IE22.PaperChallenge"],
}




def neutralize_doc_comments(text: str) -> str:
    """Keep documentation text without dangling declaration-doc syntax."""
    out, index, depth, string = [], 0, 0, False
    while index < len(text):
        char = text[index]
        pair = text[index:index+2]
        if string:
            out.append(char)
            if char == "\\" and index + 1 < len(text):
                out.append(text[index+1]); index += 2; continue
            if char == '"': string = False
            index += 1; continue
        if depth:
            if pair == "/-": depth += 1; out.append(pair); index += 2
            elif pair == "-/": depth -= 1; out.append(pair); index += 2
            else: out.append(char); index += 1
            continue
        if text[index:index+3] == "/--":
            out.append("/- "); depth = 1; index += 3
        elif pair == "/-":
            out.append(pair); depth = 1; index += 2
        elif pair == "--":
            end = text.find("\n", index)
            if end < 0: out.append(text[index:]); break
            out.append(text[index:end+1]); index = end + 1
        elif char == '"':
            string = True; out.append(char); index += 1
        else:
            out.append(char); index += 1
    return "".join(out)


def space_plain_relations(text: str) -> str:
    """Disambiguate an unadorned relation followed by an ASCII operand.

    Comments, strings, and genuinely adorned operators such as less-or-equal
    almost everywhere are untouched. Only lexical whitespace is introduced.
    """
    clean = source_mask(text)
    positions = [i for i, char in enumerate(clean) if char in "≤≥" and
        i+1 < len(clean) and re.match(r"[A-Za-z0-9_(]", clean[i+1])]
    for index in reversed(positions):
        before = "" if index == 0 or text[index-1].isspace() else " "
        after = "" if index+1 == len(text) or text[index+1].isspace() else " "
        text = text[:index] + before + text[index] + after + text[index+1:]
    return text


def solution_import_roots(entry: dict, proof_roots: list[str]) -> list[str]:
    """Avoid co-importing independent TR-04 implementations with shared names.

    Every inventoried local source still has to build as its own graph node.
    The other entries retain their previously generated imports byte for byte.
    """
    if entry["id"] == "TR-04":
        return list(dict.fromkeys(target["original_solution_module"]
            for target in entry["targets"]))
    return list(proof_roots)


def refresh_entry_inventory(entries: list[dict]) -> None:
    """Refresh the concise inventory from current, hash-checked entry records."""
    primary = {entry["id"]: entry for entry in load_json(PRIMARY)["entries"]}
    rows = []
    for entry in sorted(entries, key=lambda item: item["id"]):
        for output in entry["outputs"]:
            if sha256((ROOT / output["path"]).read_bytes()) != output["sha256"]:
                raise ValueError(f"Entry output changed outside its generator: {output['path']}")
        primary_names = entry.get("primary_theorem_names", list(dict.fromkeys(
            name for target in primary[entry["id"]]["targets"] for name in target["theorem_names"])))
        rows.append({"id": entry["id"], "theorem_names": entry["theorem_names"],
            "primary_theorem_names": primary_names,
            "supporting_theorem_names": entry.get("supporting_theorem_names", []),
            "challenge_lines": entry["challenge_lines"], "challenge_bytes": entry["challenge_bytes"],
            "challenge_imports": entry["challenge_direct_imports"],
            "solution_import_roots": entry.get("solution_import_roots", entry["solution_proof_roots"]),
            "independently_built_proof_roots": entry.get("independently_built_proof_roots", entry["solution_proof_roots"]),
            "outputs": entry["outputs"]})
    write_json(ROOT / "audit" / "entry-surface-inventory.json", {"schema_version": 2,
        "checked_date": "2026-11-19",
        "kind": "static-entry-surface-inventory; not a Lean or Comparator result",
        "entries": rows, "entry_count": len(rows),
        "maximum_challenge_lines": max((row["challenge_lines"] for row in rows), default=0),
        "maximum_challenge_bytes": max((row["challenge_bytes"] for row in rows), default=0),
        "supporting_targets": sum(len(row["supporting_theorem_names"]) for row in rows),
        "lean_build_run_by_this_helper": False, "kernel_replay_run": False})


def apply_interface_overrides(project: str, outputs: dict[str, bytes]):
    """Apply explicit literal final-render overrides without changing archives.

    patches/interfaces/ID.json has schema_version=1 and records with path,
    edits=[{old,new,occurrences,reason}], and optional before/after_sha256.
    Paths may be Challenge.lean/Solution.lean or full project-relative paths.
    Every edit count and optional hash is checked before any output is written.
    """
    override_file = ROOT / "patches" / "interfaces" / (project + ".json")
    if not override_file.is_file():
        return outputs, []
    patch = load_json(override_file)
    if patch.get("schema_version") != 1:
        raise ValueError("Unsupported interface override schema: " + project)
    current = dict(outputs)
    log = []
    for record in patch.get("records", []):
        name = record["path"]
        if name in {"Challenge.lean", "Solution.lean"}:
            name = f"projects/{project}/{name}"
        checked_path(name)
        if name not in current or name not in {f"projects/{project}/Challenge.lean", f"projects/{project}/Solution.lean"}:
            raise ValueError("Interface override is outside the selected entry: " + name)
        before = current[name]
        if record.get("before_sha256") and record["before_sha256"] != sha256(before):
            raise ValueError("Interface override input hash mismatch: " + name)
        text = before.decode("utf-8")
        for edit in record["edits"]:
            old, new = edit["old"], edit["new"]
            count = edit.get("occurrences", edit.get("count"))
            if not old or not isinstance(count, int) or count < 1 or text.count(old) != count:
                raise ValueError("Interface override literal count mismatch: " + name)
            text = text.replace(old, new)
        after = text.encode("utf-8")
        if record.get("after_sha256") and record["after_sha256"] != sha256(after):
            raise ValueError("Interface override output hash mismatch: " + name)
        current[name] = after
        log.append({"path": name, "before_sha256": sha256(before), "after_sha256": sha256(after), "override": override_file.relative_to(ROOT).as_posix(), "override_sha256": sha256(override_file.read_bytes())})
    return current, log


def capture(source_root: Path, force: bool):
    primary = load_json(PRIMARY)
    source_root = source_root.resolve(strict=True)
    inputs = {}
    records = []
    for entry in primary["entries"]:
        project = entry["id"]
        for target in entry["targets"]:
            names = [target["original_challenge_module"].replace(".", "/") + ".lean", target["original_config"]]
            for rel in names:
                key = f"projects/{project}/{rel}"
                checked_path(key)
                data = (source_root / "problems" / project / Path(rel)).read_bytes()
                if key in inputs:
                    if inputs[key] != data:
                        raise ValueError(f"Conflicting source snapshot: {key}")
                    continue
                inputs[key] = data
                records.append({"path": key, "sha256": sha256(data), "bytes": len(data), "kind": "original-challenge" if rel.endswith(".lean") else "original-comparator-config"})
    # Capture statement-only helper modules absent from the proof-source archive.
    # They remain archived input, not additional unported regular Lean files.
    _, proof_sources = read_archive()
    queue = [(key, data) for key, data in inputs.items() if key.endswith(".lean")]
    seen_modules = set()
    while queue:
        key, data = queue.pop()
        if key in seen_modules:
            continue
        seen_modules.add(key)
        project = key.split("/")[1]
        for dependency in imports(data):
            dep_key = module_key(project, dependency)
            if dep_key in proof_sources or dep_key in inputs:
                continue
            rel = dependency.replace(".", "/") + ".lean"
            original = source_root / "problems" / project / Path(rel)
            if not original.is_file():
                if re.match(r"^(Mathlib|Lean|Init|Std|Batteries|Aesop|Qq|LeanCert)(\.|$)", dependency):
                    continue
                raise ValueError(f"Unresolved original local statement import: {dependency}")
            helper = original.read_bytes()
            inputs[dep_key] = helper
            records.append({"path": dep_key, "sha256": sha256(helper), "bytes": len(helper), "kind": "auxiliary-original-statement-source"})
            queue.append((dep_key, helper))
    records.sort(key=lambda x: x["path"])
    stream = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=stream, mtime=0) as gz:
        with tarfile.open(mode="w|", fileobj=gz, format=tarfile.PAX_FORMAT) as tf:
            for record in records:
                key = record["path"]
                info = tarfile.TarInfo(key)
                info.size = len(inputs[key])
                info.mode, info.uid, info.gid, info.mtime = 0o644, 0, 0, 0
                info.uname = info.gname = ""
                tf.addfile(info, io.BytesIO(inputs[key]))
    data = stream.getvalue()
    if STATEMENTS.exists() and STATEMENTS.read_bytes() != data and not force:
        raise ValueError("Original statement archive differs; review before using --force")
    STATEMENTS.parent.mkdir(parents=True, exist_ok=True)
    STATEMENTS.write_bytes(data)
    manifest = {"schema_version": 1, "snapshot_date": "2026-11-19", "primary_targets_sha256_at_capture": sha256(PRIMARY.read_bytes()), "archive": STATEMENTS.relative_to(ROOT).as_posix(), "archive_sha256": sha256(data), "archive_bytes": len(data), "inputs": records}
    write_json(STATEMENT_MANIFEST, manifest)
    return {"archive": manifest["archive"], "archive_sha256": manifest["archive_sha256"], "input_count": len(records)}


def read_inputs():
    _, sources = read_archive()
    manifest = load_json(STATEMENT_MANIFEST)
    archive_bytes = STATEMENTS.read_bytes()
    if sha256(archive_bytes) != manifest["archive_sha256"]:
        raise ValueError("Original statement archive SHA256 mismatch")
    expected = {x["path"]: x for x in manifest["inputs"]}
    seen = set()
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:gz") as tf:
        for member in tf:
            key = checked_path(member.name).as_posix()
            if not member.isfile() or key not in expected or key in seen:
                raise ValueError(f"Unexpected statement archive member: {key}")
            seen.add(key)
            data = tf.extractfile(member).read()
            if len(data) != expected[key]["bytes"] or sha256(data) != expected[key]["sha256"]:
                raise ValueError(f"Statement source hash mismatch: {key}")
            if key in sources and sources[key] != data:
                raise ValueError(f"Source and statement archives disagree: {key}")
            sources[key] = data
    if seen != set(expected):
        raise ValueError("Missing statement archive member")
    return sources


IMPORT = re.compile(r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+([^\r\n]+)", re.M)
COMMAND = re.compile(r"^(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped|public)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|namespace|section|end|open|set_option|attribute|variable|universe|notation|macro|elab|syntax|initialize|example|export|deriving|infixl|infixr|prefix|postfix)\b([^\r\n]*)", re.M)


def imports(data: bytes):
    clean = source_mask(data.decode("utf-8-sig"))
    return [mod for m in IMPORT.finditer(clean) for mod in m.group(1).split()]


def module_key(project: str, module: str):
    return f"projects/{project}/{module.replace('.', '/')}.lean"


def module_closure(project: str, roots: list[str], sources):
    ordered, active, done, external = [], set(), set(), set()
    def visit(module):
        key = module_key(project, module)
        if key not in sources:
            if module in REVIEWED_UNUSED_UTILITY_IMPORTS.get(project, set()):
                external.add(module)
                return
            if not re.match(r"^(Mathlib|Lean|Init|Std)(\.|$)", module):
                raise ValueError(f"Challenge requires an unavailable or noncanonical external import: {module}")
            external.add(module)
            return
        if module in done:
            return
        if module in active:
            raise ValueError(f"Cyclic local imports: {module}")
        active.add(module)
        for dependency in imports(sources[key]):
            visit(dependency)
        active.remove(module)
        done.add(module)
        ordered.append(module)
    for root in roots:
        visit(root)
    return ordered, external


def scope_closures(body: str):
    """Close only formerly EOF-closed command scopes; refuse unmatched names."""
    clean = source_mask(body)
    stack = []
    for match in COMMAND.finditer(clean):
        kind, rest = match.group(1), match.group(2).strip()
        if kind in ("namespace", "section"):
            name = rest.split()[0] if rest else ""
            stack.append((kind, name))
        elif kind == "end":
            name = rest.split()[0] if rest else ""
            if not stack:
                raise ValueError("Unmatched end command while isolating source context")
            if not name:
                stack.pop()
            else:
                index = next((i for i in range(len(stack) - 1, -1, -1) if stack[i][1] == name), None)
                if index is None:
                    raise ValueError(f"Unmatched named end command: {name}")
                del stack[index:]
    return ["end" + (" " + name if name else "") for _, name in reversed(stack)]


def body_without_header(data: bytes):
    text = data.decode("utf-8-sig")
    clean = source_mask(text)
    spans = []
    header = re.match(r"\s*module\b[^\r\n]*(?:\r?\n|$)", clean)
    if header:
        # Keep any leading comments and notices by removing only command text.
        at = clean.find("module", header.start(), header.end())
        spans.append((at, header.end()))
    spans.extend((match.start(), match.end()) for match in IMPORT.finditer(clean))
    spans.extend((match.start(), match.end()) for match in re.finditer(r"@\[\s*expose\s*\]\s*public\s+section\b", clean))
    # These checking directives do not define any mathematical objects or proofs.
    spans.extend((match.start(), match.end()) for match in re.finditer(r"^[ \t]*(?:set_option[ \t]+leancert\.[^\r\n]*|#assert_trust[^\r\n]*|#print[ \t]+axioms[^\r\n]*|#check[^\r\n]*)", clean, re.M))
    for start, finish in sorted(spans, reverse=True):
        text = text[:start] + text[finish:]
    return text


def selected_statement_body(body: str, selected: set[str]):
    """Filter only theorem commands in the original small statement modules.

    Non-target helper theorem dependencies are refused, rather than assumed.
    Definition/helper modules are not filtered by this routine.
    """
    clean = source_mask(body)
    commands = list(COMMAND.finditer(clean))
    remove = []
    stack = []
    found = set()
    removed_names = []
    for index, match in enumerate(commands):
        kind, rest = match.group(1), match.group(2).strip()
        if kind == "namespace":
            stack.append(rest.split()[0])
        elif kind == "end":
            if rest:
                name = rest.split()[0]
                position = next((i for i in range(len(stack)-1, -1, -1) if stack[i] == name), None)
                if position is not None:
                    del stack[position:]
            # Anonymous sections do not change namespace names.
        elif kind in ("theorem", "lemma"):
            name = rest.split()[0]
            qualified = ".".join(stack + [name])
            if qualified in selected:
                found.add(qualified)
            else:
                finish = commands[index + 1].start() if index + 1 < len(commands) else len(body)
                remove.append((match.start(), finish))
                removed_names.append(qualified)
    if found != selected:
        raise ValueError(f"Selected statement names not found in original module: {sorted(selected - found)}")
    for start, finish in reversed(remove):
        body = body[:start] + body[finish:]
    # If any selected statement type explicitly uses a removed helper theorem,
    # a full dependency-aware extractor is required instead of this small mode.
    kept_clean = source_mask(body)
    for name in removed_names:
        short = name.rsplit(".", 1)[-1]
        if re.search(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])", kept_clean):
            raise ValueError(f"Selected type may depend on removed theorem {name}; dependency pruning is required")
    return body, sorted(found), removed_names


def build_entry(entry: dict, sources, force: bool):
    project = entry["id"]
    challenge_roots = list(dict.fromkeys(x["original_challenge_module"] for x in entry["targets"]))
    names_by_module = {}
    for target in entry["targets"]:
        names_by_module.setdefault(target["original_challenge_module"], set()).update(target["theorem_names"])
    ordered, external = module_closure(project, challenge_roots, sources)
    omitted_modules = []
    mode = "exact-whole-import-closure with selected statement filtering"
    if project in REVIEWED_MODULE_PRUNING:
        full_order = ordered
        ordered = REVIEWED_MODULE_PRUNING[project]
        if not set(ordered).issubset(full_order) or not set(challenge_roots).issubset(ordered):
            raise ValueError("Reviewed module pruning no longer matches the source closure")
        omitted_modules = [module for module in full_order if module not in ordered]
        mode = "reviewed module pruning; copied semantic declaration bodies and selected statement types unchanged"
    if project in REVIEWED_OMITTED_HELPER_MODULES:
        excluded = REVIEWED_OMITTED_HELPER_MODULES[project]
        if not excluded.issubset(ordered):
            raise ValueError("Reviewed omitted helper modules no longer match source closure")
        omitted_modules += [module for module in ordered if module in excluded]
        ordered = [module for module in ordered if module not in excluded]
        mode = "reviewed module pruning; semantic definition bodies and selected statement types unchanged"
    pieces = ["module\n\npublic import Mathlib\n\n@[expose] public section\n\n/-!\nStandalone statement surface for " + ", ".join(entry["problem_ids"]) + ".\nDefinitions and selected theorem types are retained from the original sources.\nHistorical notices below are preserved; current review status is in the audit records.\n-/\n"]
    inlined = []
    for module in ordered:
        key = module_key(project, module)
        body = body_without_header(sources[key])
        removed = []
        if module in names_by_module:
            body, found, removed = selected_statement_body(body, names_by_module[module])
        if re.search(r"\b(?:LeanCert|leancert)\b|#assert_trust\b", source_mask(body)):
            raise ValueError(f"Retained body still uses forbidden utility declarations: {module}")
        unclosed = scope_closures(body)
        pieces.append("\nsection -- Isolate source-module options, opened names, and local attributes.\n/- Original module: " + module + " -/\n" + body.rstrip() + "\n" + "".join(x + "\n" for x in unclosed) + "end\n")
        inlined.append({"module": module, "original_path": key, "original_sha256": sha256(sources[key]), "removed_unselected_theorems": removed, "formerly_eof_closed_scopes": unclosed})
    challenge = neutralize_doc_comments("\n".join(pieces)).encode("utf-8")
    lines = len(challenge.splitlines())
    if lines > 1000 or len(challenge) > 100 * 1024:
        raise ValueError(f"{project} exact whole-closure Challenge exceeds caps ({lines} lines, {len(challenge)} bytes); declaration dependency pruning is required")
    architecture = load_json(ROOT / "docs" / "build-architecture.json")
    roots = next(x["roots"] for x in architecture["minimum_claim_proof_closure"]["projects"] if x["project"] == project)
    if "Solution" in roots:
        raise ValueError(f"{project} has an existing Solution root; choose a noncolliding public solution module")
    import_roots = solution_import_roots(entry, roots)
    solution = ("module\n\n" + "".join("public import " + module + "\n" for module in import_roots) + "\n@[expose] public section\n\n/- All proof roots mapped to the current paper, including auxiliary and prose claims,\nare compiled through these imports. Selected theorem names remain unchanged. -/\n").encode("utf-8")
    config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": list(dict.fromkeys(name for target in entry["targets"] for name in target["theorem_names"])), "definition_names": [], "enable_nanoda": True, "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
    outputs = {f"projects/{project}/Challenge.lean": challenge, f"projects/{project}/Solution.lean": solution, f"projects/{project}/comparator.json": (json.dumps(config, indent=2) + "\n").encode("utf-8")}
    outputs, interface_overrides = apply_interface_overrides(project, outputs)
    challenge = outputs[f"projects/{project}/Challenge.lean"]
    lines = len(challenge.splitlines())
    if lines > 1000 or len(challenge) > 100 * 1024:
        raise ValueError(f"{project} final interface override exceeds Challenge limits")
    previous = load_json(INTERFACES) if INTERFACES.exists() else {"entries": []}
    old = next((x for x in previous["entries"] if x["id"] == project), None)
    previous_hashes = {x["path"]: x["sha256"] for x in old["outputs"]} if old else {}
    for name, data in outputs.items():
        target = ROOT / Path(name)
        if target.exists() and target.read_bytes() != data and not force:
            if previous_hashes.get(name) != sha256(target.read_bytes()):
                raise ValueError(f"Refusing to overwrite hand-edited entry file: {name}")
    for name, data in outputs.items():
        target = ROOT / Path(name)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    result = {"id": project, "status": "generated-static; Lean 4.35 build and official acceptance not yet established", "mode": mode, "omitted_helper_modules": omitted_modules, "challenge_lines": lines, "challenge_bytes": len(challenge), "challenge_direct_imports": ["Mathlib"], "original_external_imports": sorted(external), "applied_interface_overrides": interface_overrides, "discarded_nonmathematical_utility_imports": sorted(external.intersection(REVIEWED_UNUSED_UTILITY_IMPORTS.get(project, set()))), "theorem_names": config["theorem_names"], "solution_proof_roots": roots, "solution_import_roots": import_roots, "independently_built_proof_roots": roots, "inlined_sources": inlined, "outputs": [{"path": name, "sha256": sha256(data), "bytes": len(data)} for name, data in outputs.items()]}
    previous["schema_version"] = 1
    previous["generator_sha256"] = sha256(Path(__file__).read_bytes())
    previous["entries"] = sorted([x for x in previous["entries"] if x["id"] != project] + [result], key=lambda x: x["id"])
    write_json(INTERFACES, previous)
    refresh_entry_inventory(previous["entries"])
    return {key: result[key] for key in ("id", "status", "challenge_lines", "challenge_bytes", "theorem_names")}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_subparsers(dest="action", required=True)
    cp = actions.add_parser("capture")
    cp.add_argument("--source-root", type=Path, required=True)
    cp.add_argument("--force", action="store_true")
    bp = actions.add_parser("build")
    bp.add_argument("--ids", nargs="+", required=True)
    bp.add_argument("--force", action="store_true")
    args = parser.parse_args()
    try:
        if args.action == "capture":
            result = capture(args.source_root, args.force)
        else:
            sources = read_inputs()
            entries = load_json(PRIMARY)["entries"]
            known = {x["id"] for x in entries}
            if set(args.ids) - known:
                raise ValueError(f"Unknown project IDs: {sorted(set(args.ids) - known)}")
            result = [build_entry(next(x for x in entries if x["id"] == project), sources, args.force) for project in args.ids]
    except (OSError, ValueError, KeyError, tarfile.TarError) as error:
        parser.exit(1, f"Entry interface generation failed: {error}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
