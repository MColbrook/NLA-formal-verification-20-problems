#!/usr/bin/env python3
"""Capture, stage, and verify the byte-preserving source promotion.

This helper does not run Lean, install dependencies, contact a remote service,
create a Git repository, or claim toolchain compatibility. Run it from anywhere:

  python scripts/stage_sources.py capture --source-root ../lean
  python scripts/stage_sources.py stage
  python scripts/stage_sources.py verify

Capture is only for regenerating the canonical source archive from the original
workspace. Ordinary standalone rebuilding reads the included archive. By
default stage refuses to overwrite hand-edited generated source files. Existing
project pin files must already exist and are left alone; archival pins are never
restored into the modern source tree. Regenerate missing current build inputs
with scripts/pin_mathlib_dependencies.py before staging. Use --force only to
deliberately restore generated Lean sources.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile

ROOT = Path(__file__).resolve().parents[1]
ARCHITECTURE = ROOT / "docs" / "build-architecture.json"
SOURCE_MANIFEST = ROOT / "audit" / "source-input-manifest.json"
PORT_MANIFEST = ROOT / "audit" / "source-port-manifest.json"
ARCHIVE = ROOT / "archives" / "lean4.33.1-mapped-claim-sources.tar.gz"
PIN_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
COVERAGE_FILES = ("paper-map.json", "statement-coverage.json", "additional-claims.json", "verification-targets.json")
DATE = "2026-11-19"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json(file: Path):
    return json.loads(file.read_text(encoding="utf-8-sig"))


def write_json(file: Path, data) -> None:
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")


def checked_path(value: str) -> PurePosixPath:
    p = PurePosixPath(value)
    if p.is_absolute() or not p.parts or any(x in ("", ".", "..") for x in p.parts):
        raise ValueError(f"Unsafe archive path: {value!r}")
    if "\\" in value or ":" in value or value != p.as_posix():
        raise ValueError(f"Noncanonical archive path: {value!r}")
    return p


def source_mask(text: str) -> str:
    """Mask comments and string literals while retaining offsets and newlines."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if depth:
            if c == "/" and n == "-":
                depth += 1
                out[i:i + 2] = [" ", " "]
                i += 2
            elif c == "-" and n == "/":
                depth -= 1
                out[i:i + 2] = [" ", " "]
                i += 2
            else:
                out[i] = "\n" if c == "\n" else " "
                i += 1
        elif string:
            out[i] = "\n" if c == "\n" else " "
            if c == "\\" and n:
                out[i + 1] = "\n" if n == "\n" else " "
                i += 2
            else:
                if c == '"':
                    string = False
                i += 1
        elif c == "/" and n == "-":
            depth = 1
            out[i:i + 2] = [" ", " "]
            i += 2
        elif c == "-" and n == "-":
            while i < len(text) and text[i] != "\n":
                out[i] = " "
                i += 1
        elif c == '"':
            string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("Unterminated comment or string in source")
    return "".join(out)


def promote(original: bytes) -> tuple[bytes, dict]:
    """Only change module/import/visibility directives, retaining proof text."""
    text = original.decode("utf-8")
    bom = "\ufeff" if text.startswith("\ufeff") else ""
    if bom:
        text = text[1:]
    newline = "\r\n" if "\r\n" in text else "\n"
    actions = {"module_header_added": False, "imports_made_public": 0, "exposed_public_section_added": False}
    mask = source_mask(text)
    if not re.match(r"\s*module\b", mask):
        text = "module" + newline + newline + text
        actions["module_header_added"] = True
    mask = source_mask(text)
    # Match only actual import-command prefixes, never comment/string contents.
    # No selected source uses meta import; support it without changing its role.
    import_re = re.compile(r"^(?P<indent>[ \t]*)(?P<public>public[ \t]+)?(?P<meta>meta[ \t]+)?import\b", re.M)
    matches = list(import_re.finditer(mask))
    for match in reversed(matches):
        if match.group("public") is None:
            at = match.start() + len(match.group("indent"))
            text = text[:at] + "public " + text[at:]
            actions["imports_made_public"] += 1
    mask = source_mask(text)
    # Existing module-system source already contains the requested global
    # visibility section. Do not create a second section in those modules.
    has_section = re.search(r"@\[\s*expose\s*\]\s*public\s+section\b", mask)
    if not has_section:
        imports = list(import_re.finditer(mask))
        if imports:
            line_end = text.find("\n", imports[-1].end())
            insert = len(text) if line_end < 0 else line_end + 1
            separator = newline if line_end < 0 else ""
            text = text[:insert] + separator + newline + "@[expose] public section" + newline + text[insert:]
        else:
            header = re.match(r"\s*module\b", source_mask(text))
            assert header is not None
            line_end = text.find("\n", header.end())
            insert = len(text) if line_end < 0 else line_end + 1
            separator = newline if line_end < 0 else ""
            text = text[:insert] + separator + newline + "@[expose] public section" + newline + text[insert:]
        actions["exposed_public_section_added"] = True
    output = (bom + text).encode("utf-8")
    return output, actions



COMPATIBILITY_INDEX = None


def apply_compatibility_patches(name: str, original: bytes) -> tuple[bytes, list[dict]]:
    """Apply only reviewed literal replacements with exact before/after hashes."""
    global COMPATIBILITY_INDEX
    if COMPATIBILITY_INDEX is None:
        COMPATIBILITY_INDEX = {}
        for patch_file in sorted((ROOT / "patches" / "compatibility").glob("*.json")):
            patch = load_json(patch_file)
            if patch.get("schema_version") != 1:
                raise ValueError(f"Unsupported compatibility patch schema: {patch_file.name}")
            patch_digest = sha256(patch_file.read_bytes())
            for record in patch.get("records", []):
                checked_path(record["path"])
                COMPATIBILITY_INDEX.setdefault(record["path"], []).append((patch_file, patch_digest, record))
    current = original
    applied = []
    for patch_file, patch_digest, record in COMPATIBILITY_INDEX.get(name, []):
        if sha256(current) != record["before_sha256"]:
            raise ValueError(f"Compatibility patch input mismatch: {name} ({patch_file.name})")
        text = current.decode("utf-8")
        for edit in record["edits"]:
            old, new, count = edit["old"], edit["new"], edit["occurrences"]
            if not old or not isinstance(count, int) or count < 1 or text.count(old) != count:
                raise ValueError(f"Compatibility edit count mismatch: {name} ({patch_file.name})")
            text = text.replace(old, new)
        current = text.encode("utf-8")
        if sha256(current) != record["after_sha256"]:
            raise ValueError(f"Compatibility patch output mismatch: {name} ({patch_file.name})")
        applied.append({"patch": patch_file.relative_to(ROOT).as_posix(), "patch_sha256": patch_digest, "before_sha256": record["before_sha256"], "after_sha256": record["after_sha256"]})
    return current, applied


def capture(source_root: Path, force: bool) -> dict:
    architecture = load_json(ARCHITECTURE)
    source_root = source_root.resolve(strict=True)
    entries = []
    payload = {}
    for project in architecture["minimum_claim_proof_closure"]["projects"]:
        project_id = project["project"]
        for record in project["files"]:
            rel = f"problems/{project_id}/{record['path']}"
            archive_path = f"projects/{project_id}/{record['path']}"
            checked_path(archive_path)
            data = (source_root / Path(rel)).read_bytes()
            if sha256(data) != record["sha256"] or len(data) != record["bytes"]:
                raise ValueError(f"Source no longer matches reviewed inventory: {rel}")
            payload[archive_path] = data
            entries.append({"archive_path": archive_path, "original_relative_path": rel, "kind": "lean-source", "sha256": sha256(data), "bytes": len(data), "module": record["module"]})
        for pin in PIN_FILES:
            rel = f"problems/{project_id}/{pin}"
            archive_path = f"projects/{project_id}/{pin}"
            data = (source_root / Path(rel)).read_bytes()
            payload[archive_path] = data
            entries.append({"archive_path": archive_path, "original_relative_path": rel, "kind": "original-build-pin", "sha256": sha256(data), "bytes": len(data)})
    for name in COVERAGE_FILES:
        data = (source_root / name).read_bytes()
        archive_path = f"metadata/{name}"
        payload[archive_path] = data
        entries.append({"archive_path": archive_path, "original_relative_path": name, "kind": "original-coverage-metadata", "sha256": sha256(data), "bytes": len(data)})
    entries.sort(key=lambda entry: entry["archive_path"])
    if len({entry["archive_path"].casefold() for entry in entries}) != len(entries):
        raise ValueError("Archive has a duplicate or case-colliding path")
    archive_bytes = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=archive_bytes, mtime=0) as gz:
        with tarfile.open(mode="w|", fileobj=gz, format=tarfile.PAX_FORMAT) as tf:
            for entry in entries:
                name = entry["archive_path"]
                info = tarfile.TarInfo(name)
                info.size = len(payload[name])
                info.mode, info.mtime, info.uid, info.gid = 0o644, 0, 0, 0
                info.uname = info.gname = ""
                tf.addfile(info, io.BytesIO(payload[name]))
    data = archive_bytes.getvalue()
    if ARCHIVE.exists() and ARCHIVE.read_bytes() != data and not force:
        raise ValueError("Canonical source archive differs; use --force only after reviewing the source change")
    ARCHIVE.parent.mkdir(parents=True, exist_ok=True)
    ARCHIVE.write_bytes(data)
    manifest = {"schema_version": 1, "snapshot_date": DATE, "scope": "Exact static import closure of all mapped named statements, prose claims, and supporting proof files; original build pins and four coverage ledgers", "manuscript_sha256": architecture["manuscript"]["sha256"], "source_toolchain": "leanprover/lean4:v4.33.1", "archive": ARCHIVE.relative_to(ROOT).as_posix(), "archive_sha256": sha256(data), "archive_bytes": len(data), "lean_source_count": sum(x["kind"] == "lean-source" for x in entries), "input_count": len(entries), "inputs": entries}
    write_json(SOURCE_MANIFEST, manifest)
    return {key: manifest[key] for key in ("archive", "archive_sha256", "archive_bytes", "lean_source_count", "input_count")}


def read_archive() -> tuple[dict, dict[str, bytes]]:
    manifest = load_json(SOURCE_MANIFEST)
    data = ARCHIVE.read_bytes()
    if sha256(data) != manifest["archive_sha256"]:
        raise ValueError("Canonical source archive SHA256 mismatch")
    expected = {x["archive_path"]: x for x in manifest["inputs"]}
    contents = {}
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
        for member in tf:
            name = checked_path(member.name).as_posix()
            if not member.isfile() or name not in expected or name in contents:
                raise ValueError(f"Unexpected, duplicate, or nonregular archive member: {name}")
            if member.size != expected[name]["bytes"]:
                raise ValueError(f"Archive member size mismatch: {name}")
            handle = tf.extractfile(member)
            if handle is None:
                raise ValueError(f"Cannot read archive member: {name}")
            content = handle.read()
            if sha256(content) != expected[name]["sha256"]:
                raise ValueError(f"Archive member SHA256 mismatch: {name}")
            contents[name] = content
    if set(contents) != set(expected):
        raise ValueError("Canonical archive is missing listed inputs")
    return manifest, contents


def stage(force: bool) -> dict:
    source_manifest, contents = read_archive()
    missing_build_inputs = [entry["archive_path"] for entry in source_manifest["inputs"]
        if entry["kind"] == "original-build-pin" and not (ROOT / Path(entry["archive_path"])).is_file()]
    if missing_build_inputs:
        raise ValueError("Current project build inputs are missing; archival Lean 4.33.1 pins will not be restored. "
            "Run python scripts/pin_mathlib_dependencies.py to regenerate the canonical current configuration first. Missing: "
            + ", ".join(missing_build_inputs))
    previous = load_json(PORT_MANIFEST) if PORT_MANIFEST.exists() else {}
    old_records = {x["path"]: x for x in previous.get("sources", [])}
    generated = []
    pins = []
    # Validate every write before changing any files.
    planned = []
    for entry in source_manifest["inputs"]:
        name = entry["archive_path"]
        if entry["kind"] == "lean-source":
            transformed, actions = promote(contents[name])
            visibility_sha256 = sha256(transformed)
            transformed, compatibility = apply_compatibility_patches(name, transformed)
            target = ROOT / Path(name)
            transformed_sha = sha256(transformed)
            if target.exists() and sha256(target.read_bytes()) != transformed_sha and not force:
                old = old_records.get(name)
                if old is None or sha256(target.read_bytes()) != old["staged_sha256"]:
                    raise ValueError(f"Refusing to overwrite changed source: {name}; inspect it or use --force")
            if not target.exists() or target.read_bytes() != transformed:
                planned.append((target, transformed))
            generated.append({"path": name, "module": entry["module"], "original_sha256": entry["sha256"], "original_bytes": entry["bytes"], "staged_sha256": transformed_sha, "staged_bytes": len(transformed), "transformations": actions, "visibility_promoted_sha256": visibility_sha256, "compatibility_patches": compatibility, "changed": transformed != contents[name]})
        elif entry["kind"] == "original-build-pin":
            target = ROOT / Path(name)
            pins.append({"path": name, "original_sha256": entry["sha256"], "status": "Current configuration is required and preserved byte for byte; original historical configuration remains only in the archive"})
    for target, data in planned:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    result = {"schema_version": 1, "snapshot_date": DATE, "transformation": "Module-system visibility promotion plus explicit hash-bound compatibility patches; mathematical changes and proof replacements are declared in each patch record", "verification_status": "Static byte and directive verification only; no Lean build or kernel replay", "source_archive_sha256": source_manifest["archive_sha256"], "source_manifest": SOURCE_MANIFEST.relative_to(ROOT).as_posix(), "script_sha256": sha256(Path(__file__).read_bytes()), "source_count": len(generated), "changed_source_count": sum(x["changed"] for x in generated), "source_bytes": sum(x["original_bytes"] for x in generated), "staged_bytes": sum(x["staged_bytes"] for x in generated), "sources": generated, "original_build_pins": pins}
    write_json(PORT_MANIFEST, result)
    return {key: result[key] for key in ("source_count", "changed_source_count", "source_bytes", "staged_bytes", "verification_status")}


def verify() -> dict:
    source_manifest, contents = read_archive()
    port_manifest = load_json(PORT_MANIFEST)
    records = {x["path"]: x for x in port_manifest["sources"]}
    if port_manifest["source_archive_sha256"] != source_manifest["archive_sha256"]:
        raise ValueError("Source and port manifests bind different archives")
    if port_manifest["script_sha256"] != sha256(Path(__file__).read_bytes()):
        raise ValueError("Staging helper changed since the recorded promotion")
    failures = []
    modules_added = imports_promoted = exposed_added = 0
    maximum_lines = 0
    for entry in source_manifest["inputs"]:
        if entry["kind"] != "lean-source":
            continue
        name = entry["archive_path"]
        expected, actions = promote(contents[name])
        visibility_promoted_sha256 = sha256(expected)
        expected, compatibility = apply_compatibility_patches(name, expected)
        target = ROOT / Path(name)
        if not target.is_file():
            failures.append(f"Missing staged source: {name}")
            continue
        actual = target.read_bytes()
        record = records.get(name)
        if actual != expected or record is None or sha256(actual) != record["staged_sha256"]:
            failures.append(f"Changed staged source: {name}")
        if record is not None and record["original_sha256"] != entry["sha256"]:
            failures.append(f"Original-source binding mismatch: {name}")
        if record is not None and record.get("compatibility_patches", []) != compatibility:
            failures.append(f"Compatibility-patch provenance mismatch: {name}")
        if record is not None and record.get("visibility_promoted_sha256") != visibility_promoted_sha256:
            failures.append(f"Visibility-promotion hash mismatch: {name}")
        if record is not None and record.get("transformations") != actions:
            failures.append(f"Visibility-promotion action mismatch: {name}")
        clean = source_mask(actual.decode("utf-8-sig"))
        if not re.match(r"\s*module\b", clean):
            failures.append(f"Missing first module command: {name}")
        if re.search(r"^[ \t]*(?:meta[ \t]+)?import\b", clean, re.M):
            failures.append(f"Unpromoted import command: {name}")
        if not re.search(r"@\[\s*expose\s*\]\s*public\s+section\b", clean):
            failures.append(f"Missing exposed public section: {name}")
        lines = len(actual.splitlines())
        maximum_lines = max(maximum_lines, lines)
        if lines > 10000:
            failures.append(f"Source exceeds current 10000-line cap: {name}")
        modules_added += int(actions["module_header_added"])
        imports_promoted += actions["imports_made_public"]
        exposed_added += int(actions["exposed_public_section_added"])
    if len(records) != source_manifest["lean_source_count"]:
        failures.append("Port source count differs from archived source count")
    if failures:
        raise ValueError("\n".join(failures))
    return {"static_checks_passed": True, "source_count": source_manifest["lean_source_count"], "archive_sha256": source_manifest["archive_sha256"], "module_headers_added": modules_added, "imports_made_public": imports_promoted, "exposed_public_sections_added": exposed_added, "maximum_source_lines": maximum_lines, "lean_build_run": False, "kernel_replay_run": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    actions = parser.add_subparsers(dest="action", required=True)
    capture_parser = actions.add_parser("capture", help="Create the deterministic original-byte archive from a reviewed source workspace")
    capture_parser.add_argument("--source-root", type=Path, required=True)
    capture_parser.add_argument("--force", action="store_true")
    stage_parser = actions.add_parser("stage", help="Rebuild promoted source copies from the included archive")
    stage_parser.add_argument("--force", action="store_true", help="Overwrite hand-edited source copies after deliberate review")
    actions.add_parser("verify", help="Check archive, hashes, deterministic promotion, and basic source directives without running Lean")
    args = parser.parse_args()
    try:
        if args.action == "capture":
            result = capture(args.source_root, args.force)
        elif args.action == "stage":
            result = stage(args.force)
        else:
            result = verify()
    except (OSError, ValueError, KeyError, tarfile.TarError) as error:
        parser.exit(1, f"Source staging failed: {error}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
