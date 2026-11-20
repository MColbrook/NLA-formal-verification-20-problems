#!/usr/bin/env python3
"""Check compiler-backed source-anchor eligibility; this does not render Verso HTML.

The runtime query reads the selected Challenge's server declaration ranges without
executing its initializers. ``validate_evidence`` is portable, read-only and never
launches a compiler or accesses the recorded machine-specific artifact paths.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from parallel_build import inventory

RECEIPT = "verification/challenge-anchors.json"
PUBLIC = "verification/challenge-anchors/"
DRIVER = "scripts/check_challenge_anchors.py"
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
TEMPLATE = r'''module
public import Lean
@[expose] public section
open Lean
def positionJSON (p : Position) : Json := Json.mkObj [("line",toJson p.line),("column",toJson p.column)]
def rangeJSON (r : DeclarationRange) : Json := Json.mkObj [("start",positionJSON r.pos),("end",positionJSON r.endPos)]
unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let path ← findOLean `__MODULE__
  let (mainData, mainRegion) ← CompactedRegion.read (α := ModuleData) path #[]
  let (serverData, serverRegion) ← CompactedRegion.read (α := ModuleData)
    (OLeanLevel.server.adjustFileName path) #[mainRegion]
  let (privateData, privateRegion) ← CompactedRegion.read (α := ModuleData)
    (OLeanLevel.private.adjustFileName path) #[mainRegion, serverRegion]
  let owners ← IO.mkRef (mainRegion, serverRegion, privateRegion)
  -- The exported view may represent a theorem by its axiom-like signature;
  -- its original declaration kind is retained in the private module part.
  let constants := privateData.constants ++ serverData.constants ++ mainData.constants
  let rangeEntries : Array (Name × DeclarationRanges) := match serverData.entries.find? (fun item => item.1 == declRangeExt.name) with
    | some (_, entries) => unsafeCast entries
    | none => #[]
  let mut rows : Array Json := #[]
  for name in (__NAMES__ : Array Name) do
    let info := constants.find? (fun info => info.name == name)
    let kind := match info with | some (.thmInfo _) => "theorem" | some _ => "other" | none => "missing"
    let owner := if info.isSome then some "__MODULE__" else none
    let ranges := (rangeEntries.find? (fun item => item.1 == name)).map (·.2)
    rows := rows.push <| Json.mkObj [("name",toJson name.toString),("kind",toJson kind),("module",toJson owner),("range",match ranges with | some r => rangeJSON r.range | none => Json.null),("selection",match ranges with | some r => rangeJSON r.selectionRange | none => Json.null)]
  let _ ← owners.get
  IO.println ("CHALLENGE_ANCHORS " ++ (toJson rows).compress)
  return 0
'''


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def configuration(root: Path) -> dict:
    config = load(root / "comparator.json")
    if config.get("challenge_module") != "Challenge" or config.get("definition_names", []):
        raise ValueError("This eligibility gate requires root Challenge and no definition holes")
    names = config.get("theorem_names")
    if not isinstance(names, list) or not names or len(set(names)) != len(names):
        raise ValueError("Expected distinct selected theorem names")
    if any(not isinstance(name, str) or not NAME.fullmatch(name) or name.startswith("_private.") for name in names):
        raise ValueError("Expected safe public selected names")
    return config


def query_text(config: dict) -> str:
    return TEMPLATE.replace("__MODULE__", config["challenge_module"]).replace(
        "__NAMES__", "#[" + ", ".join("`" + name for name in config["theorem_names"]) + "]")


def artifacts(rows: list, module: str = "Challenge") -> dict:
    if not isinstance(rows, list) or len(rows) != len(SUFFIXES):
        raise ValueError("Exactly five compiled Challenge artifact records are required")
    result = {}
    for row, suffix in zip(rows, SUFFIXES):
        if (not isinstance(row, dict) or not isinstance(row.get("path"), str)
            or not row["path"].replace(chr(92), "/").endswith("/" + module.replace(".", "/") + suffix)
            or not re.fullmatch(r"[0-9a-f]{64}", str(row.get("sha256", "")))
            or ("bytes" in row and (type(row["bytes"]) is not int or row["bytes"] <= 0))):
            raise ValueError("Malformed compiled Challenge artifact record: " + suffix)
        result[suffix] = row["sha256"]
    return result


def combined_build(root: Path, source_digest: str) -> dict:
    data = load(root / "verification/combined-build-status.json")
    rows = data.get("projects", [])
    if data.get("kind") != "ordinary-combined-source-compilation" or data.get("status") != "pass" or len(rows) != 1:
        raise ValueError("Fresh successful combined compilation is required")
    row = rows[0]
    for key, expected in {"id": "NLA20", "status": "pass", "source_inventory_sha256": source_digest,
                          "combined_challenge_compiled": True, "combined_solution_compiled": True,
                          "source_stable": True, "exit_code": 0}.items():
        if row.get(key) != expected:
            raise ValueError("Combined build binding mismatch: " + key)
    artifacts(row.get("challenge_artifacts"))
    return row


def inspect_declarations(source: str, module: str, names: list[str], rows: list) -> tuple[list, list]:
    """Validate actual compiler ranges and the original source token they select."""
    if not isinstance(rows, list) or [row.get("name") for row in rows if isinstance(row, dict)] != names:
        raise ValueError("Compiler output must identify every configured declaration exactly once in order")
    lines = source.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    def offset(position):
        if not isinstance(position, dict) or set(position) != {"line", "column"}:
            raise ValueError("Malformed compiler source position")
        line, column = position["line"], position["column"]
        if type(line) is not int or type(column) is not int or not 1 <= line <= len(lines) or not 0 <= column <= len(lines[line - 1].rstrip("\r\n")):
            raise ValueError("Compiler source position is outside the current Challenge")
        return offsets[line - 1] + column

    def bounds(value):
        if not isinstance(value, dict) or set(value) != {"start", "end"}:
            raise ValueError("Missing compiler-backed declaration range")
        start, end = offset(value["start"]), offset(value["end"])
        if start >= end:
            raise ValueError("Compiler-backed declaration range is empty")
        return start, end

    declarations, errors, seen = [], [], set()
    for name, row in zip(names, rows):
        try:
            if row.get("kind") != "theorem" or row.get("module") != module:
                raise ValueError("Selected name must be a theorem declared by the Challenge module")
            start, end = bounds(row.get("range"))
            first, last = bounds(row.get("selection"))
            if not start <= first < last <= end:
                raise ValueError("Name selection lies outside its declaration range")
            token = source[first:last]
            plain = token.removeprefix("_root_.")
            if not NAME.fullmatch(plain) or not (name == plain or name.endswith("." + plain)):
                raise ValueError("Compiler selection is not this declaration's explicit source name")
            if not re.search(r"\b(?:theorem|lemma)\s*$", source[start:first]):
                raise ValueError("Name is not introduced by an explicit source theorem declaration")
            if (first, last) in seen:
                raise ValueError("Selected declarations share a source-name span")
            seen.add((first, last))
            declarations.append({**row, "source_token": token})
        except ValueError as error:
            errors.append({"name": name, "message": str(error)})
    return declarations, errors


def parse_stdout(data: bytes) -> list:
    lines = [line.removeprefix("CHALLENGE_ANCHORS ") for line in data.decode("utf-8").splitlines() if line.startswith("CHALLENGE_ANCHORS ")]
    if len(lines) != 1:
        raise ValueError("Expected one compiler-backed declaration-range result")
    return json.loads(lines[0])


def validate_evidence(root: Path) -> dict:
    """Check portable source/public-output/build bindings, without executing tools."""
    root = root.resolve()
    config = configuration(root)
    source_digest = inventory(root)[1]
    build = combined_build(root, source_digest)
    receipt = load(root / RECEIPT)
    expected = {"schema_version": 1, "kind": "compiler-backed-challenge-source-anchor-eligibility",
        "status": "pass", "eligible": True, "source_inventory_sha256": source_digest,
        "challenge_source_sha256": sha((root / "Challenge.lean").read_bytes()),
        "comparator_config_sha256": sha((root / "comparator.json").read_bytes()),
        "challenge_module": config["challenge_module"], "theorem_names": config["theorem_names"],
        "compiler_version": build["compiler_version"], "compiler_sha256": build["compiler_sha256"],
        "driver_path": DRIVER, "driver_sha256": sha((root / DRIVER).read_bytes()),
        "source_stable": True, "compiler_stable": True, "driver_stable": True, "query_stable": True,
        "compiled_artifacts_stable": True, "exit_code": 0, "errors": [],
        "verso_render_performed": False, "kernel_replay_performed": False,
        "official_palomar_verification": False}
    for key, value in expected.items():
        if receipt.get(key) != value:
            raise ValueError("Challenge source-anchor receipt mismatch: " + key)
    if artifacts(receipt.get("challenge_artifacts")) != artifacts(build["challenge_artifacts"]):
        raise ValueError("Anchor query and current build used different compiled Challenge/server artifacts")
    payloads = {}
    for role in ("query", "stdout", "stderr"):
        relative = PUBLIC + role + ".txt"
        if receipt.get(role + "_path") != relative:
            raise ValueError("Unexpected public anchor-query path: " + role)
        payloads[role] = (root / relative).read_bytes()
        if sha(payloads[role]) != receipt.get(role + "_sha256"):
            raise ValueError("Changed public anchor-query artifact: " + role)
    if payloads["query"] != query_text(config).encode("utf-8"):
        raise ValueError("Public anchor query differs from the current compiler-range query")
    declarations, errors = inspect_declarations((root / "Challenge.lean").read_text(encoding="utf-8"),
        config["challenge_module"], config["theorem_names"], parse_stdout(payloads["stdout"]))
    if errors or receipt.get("declarations") != declarations or receipt.get("eligible_declarations") != len(config["theorem_names"]):
        raise ValueError("Not every selected declaration has its own eligible compiler-backed source name")
    return {"path": RECEIPT, "sha256": sha((root / RECEIPT).read_bytes()),
            "selected_declarations": len(declarations), "compiler_backed_source_names": True,
            "server_artifact_bound": True, "verso_render_performed": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--cache-dir", type=Path, default=Path(tempfile.gettempdir()) / "nla-palomar-deps-4.35.0")
    parser.add_argument("--work-dir", type=Path, default=Path(tempfile.gettempdir()) / "nla-palomar-challenge-anchors-4.35.0")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--memory-mb", type=int, default=8192)
    args = parser.parse_args()
    config = configuration(ROOT)
    source = (ROOT / "Challenge.lean").read_bytes()
    config_bytes = (ROOT / "comparator.json").read_bytes()
    digest = inventory(ROOT)[1]
    build = combined_build(ROOT, digest)
    compiler = args.lean.resolve()
    version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    compiler_digest = sha(compiler.read_bytes())
    if version != build["compiler_version"] or compiler_digest != build["compiler_sha256"]:
        raise ValueError("Anchor query must use the exact combined-build compiler")
    compiled = [{"path": str(ROOT / ".lake/build/lib/lean" / ("Challenge" + suffix)),
                 "sha256": sha((ROOT / ".lake/build/lib/lean" / ("Challenge" + suffix)).read_bytes()),
                 "bytes": (ROOT / ".lake/build/lib/lean" / ("Challenge" + suffix)).stat().st_size} for suffix in SUFFIXES]
    if artifacts(compiled) != artifacts(build["challenge_artifacts"]):
        raise ValueError("Local compiled Challenge artifacts differ from the current combined receipt")
    driver_digest = sha(Path(__file__).read_bytes())
    work = args.work_dir.resolve()
    if work == ROOT or work.is_relative_to(ROOT):
        raise ValueError("Anchor-query work directory must be outside proof inputs")
    work.mkdir(parents=True, exist_ok=True)
    query = query_text(config).encode("utf-8")
    filename = work / "ChallengeAnchors.lean"
    filename.write_bytes(query)
    packages = args.cache_dir.resolve() / ".lake/packages"
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(ROOT / ".lake/build/lib/lean")] +
        [str(packages / row["name"] / ".lake/build/lib/lean") for row in load(ROOT / "dependency-profile.json")["packages"]])
    env["LEAN_NUM_THREADS"] = "1"
    with (work / "stdout.txt").open("wb") as out, (work / "stderr.txt").open("wb") as err:
        try:
            code = subprocess.run([str(compiler), "-R", str(work), "-j1", "-M" + str(args.memory_mb),
                "--run", str(filename)], cwd=work, env=env, stdout=out, stderr=err, timeout=args.timeout).returncode
        except subprocess.TimeoutExpired:
            code = 124
            err.write(b"Compiler-backed anchor query exceeded its timeout.\n")
    stdout, stderr = (work / "stdout.txt").read_bytes(), (work / "stderr.txt").read_bytes()
    declarations, errors = [], []
    try:
        declarations, errors = inspect_declarations(source.decode("utf-8"), config["challenge_module"], config["theorem_names"], parse_stdout(stdout))
    except (ValueError, UnicodeError) as error:
        errors.append({"message": str(error)})
    stable = inventory(ROOT)[1] == digest
    artifacts_stable = all(sha(Path(row["path"]).read_bytes()) == row["sha256"] for row in compiled)
    compiler_stable = sha(compiler.read_bytes()) == compiler_digest
    driver_stable = sha(Path(__file__).read_bytes()) == driver_digest
    query_stable = filename.read_bytes() == query
    passed = code == 0 and not errors and stable and artifacts_stable and compiler_stable and driver_stable and query_stable
    receipt = {"schema_version": 1, "kind": "compiler-backed-challenge-source-anchor-eligibility",
        "status": "pass" if passed else "fail", "eligible": passed, "exit_code": code,
        "scope": "Compiler-backed declaration ranges and explicit source-name tokens; no Verso HTML rendering or publication verification is claimed.",
        "source_inventory_sha256": digest, "challenge_source_sha256": sha(source),
        "comparator_config_sha256": sha(config_bytes), "challenge_module": config["challenge_module"],
        "theorem_names": config["theorem_names"], "compiler_version": version, "compiler_sha256": compiler_digest,
        "challenge_artifacts": compiled, "driver_path": DRIVER, "driver_sha256": driver_digest,
        "source_stable": stable, "compiled_artifacts_stable": artifacts_stable,
        "compiler_stable": compiler_stable, "driver_stable": driver_stable, "query_stable": query_stable,
        "declarations": declarations, "eligible_declarations": len(declarations), "errors": errors,
        "verso_render_performed": False, "kernel_replay_performed": False, "official_palomar_verification": False}
    for role, data in (("query", query), ("stdout", stdout), ("stderr", stderr)):
        relative = PUBLIC + role + ".txt"
        path = ROOT / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        receipt[role + "_path"], receipt[role + "_sha256"] = relative, sha(data)
    (ROOT / RECEIPT).write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    if passed:
        validate_evidence(ROOT)
    print(json.dumps({"status": receipt["status"], "selected_declarations": len(config["theorem_names"]),
        "eligible_declarations": len(declarations), "errors": errors, "verso_render_performed": False}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
