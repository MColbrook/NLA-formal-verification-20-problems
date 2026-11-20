#!/usr/bin/env python3
"""Compile standalone Challenges only, using a pinned existing Mathlib cache.

This checks interface elaboration, not Solutions, Comparator matching, proof
exports, NanoDa, or whole-project build readiness. Challenges deliberately have
configured theorem placeholders. No submission proof source is modified.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--cache-dir", required=True, type=Path)
    parser.add_argument("--work-dir", type=Path, default=Path(tempfile.gettempdir()) / "nla-palomar-challenges-4.35.0")
    parser.add_argument("--report", type=Path, default=ROOT / "verification/challenge-build-status.json")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--ids", nargs="*")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 2:
        parser.error("Challenge preflight permits one or two compiler processes")
    lean = args.lean.resolve(strict=True)
    compiler_version = subprocess.run([str(lean), "--version"], capture_output=True, text=True, check=True).stdout.strip()
    if "version 4.35.0," not in compiler_version:
        parser.error("Use the exact project toolchain Lean 4.35.0")
    compiler = {"path": str(lean), "sha256": digest(lean.read_bytes()), "version": compiler_version}
    index = json.loads((ROOT / "submission-index.json").read_text(encoding="utf-8"))
    profile_file = ROOT / "dependency-profile.json"
    profile = json.loads(profile_file.read_text(encoding="utf-8"))
    if profile["toolchain"] != "leanprover/lean4:v4.35.0" or len(profile["packages"]) != 9:
        parser.error("Unexpected canonical dependency profile")
    packages = args.cache_dir.resolve(strict=True) / ".lake/packages"
    external = []
    missing_build_dirs = []
    for package in profile["packages"]:
        output = packages / package["name"] / ".lake/build/lib/lean"
        if not (packages / package["name"]).is_dir():
            parser.error("Missing pinned dependency source directory: " + package["name"])
        if not output.is_dir():
            missing_build_dirs.append(str(output))
        external.append(output)
    entries = [entry for entry in index.get("components", index["entries"]) if not args.ids or entry["id"] in args.ids]
    if args.ids and set(args.ids) != {entry["id"] for entry in entries}:
        parser.error("Unknown project id")
    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=True)
    logs = ROOT / "verification/local-builds/challenges"
    logs.mkdir(parents=True, exist_ok=True)
    started = time.time()
    results = []
    def report(final=False):
        value = {"schema_version": 1, "kind": "standalone-challenge-elaboration-only", "status": ("pass" if all(row["status"] == "pass" for row in results) else "fail") if final else "in-progress", "scope": "Native compilation of explicit statement surfaces only; Solutions and theorem proof correctness are not established by this report", "compiler": compiler, "dependency_profile_sha256": digest(profile_file.read_bytes()), "missing_unused_dependency_build_dirs": missing_build_dirs, "jobs": args.jobs, "memory_mb_per_process": args.memory_mb, "elapsed_seconds": round(time.time()-started, 3), "expected_projects": [entry["id"] for entry in entries], "projects": sorted(results, key=lambda row: row["id"]), "completed": len(results), "total": len(entries), "comparator_run": False, "kernel_replay_performed": False, "full_project_build_pass": False}
        atomic_json(args.report.resolve(), value)
        return value
    def compile_one(entry):
        project_id = entry["id"]
        project = ROOT / entry["project_path"]
        source = project / "Challenge.lean"
        original = source.read_bytes()
        source_sha256 = digest(original)
        target_dir = work / project_id
        if not target_dir.resolve().is_relative_to(work):
            raise ValueError("Unsafe temporary project path")
        target_dir.mkdir(parents=True, exist_ok=True)
        copied = target_dir / "Challenge.lean"
        copied.write_bytes(original)
        if digest(copied.read_bytes()) != source_sha256:
            raise ValueError("Challenge copy differs from source")
        output_dir = target_dir / "lib/lean"
        output_dir.mkdir(parents=True, exist_ok=True)
        output = output_dir / "Challenge.olean"
        command = [str(lean), "-j1", "-M" + str(args.memory_mb), "-o", str(output), str(copied)]
        environment = dict(os.environ)
        environment["LEAN_PATH"] = os.pathsep.join(str(path) for path in [output_dir] + external)
        environment["LEAN_NUM_THREADS"] = "1"
        log = logs / (project_id + ".log")
        begin = time.time()
        print(json.dumps({"event": "BUILD_CHALLENGE", "id": project_id}), flush=True)
        with log.open("wb") as handle:
            result = subprocess.run(command, cwd=target_dir, env=environment, stdout=handle, stderr=subprocess.STDOUT)
        stable = digest(source.read_bytes()) == source_sha256 and digest(copied.read_bytes()) == source_sha256
        artifacts = [output, output.with_suffix(".olean.private"), output.with_suffix(".olean.server"), output.with_suffix(".ir"), output.with_suffix(".ir.sig")]
        row = {"id": project_id, "status": "pass" if result.returncode == 0 and stable and all(item.is_file() for item in artifacts) else "fail", "exit_code": result.returncode, "challenge_source_sha256": source_sha256, "source_stable": stable, "copied_path": str(copied), "command": command, "elapsed_seconds": round(time.time()-begin, 3), "log": log.relative_to(ROOT).as_posix(), "log_sha256": digest(log.read_bytes()), "artifacts": [{"path": str(item), "sha256": digest(item.read_bytes())} for item in artifacts if item.is_file()]}
        atomic_json(log.with_suffix(".json"), row)
        print(json.dumps({"event": row["status"].upper(), "id": project_id, "seconds": row["elapsed_seconds"]}), flush=True)
        return row
    report()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(compile_one, entry): entry for entry in entries}
        for future in concurrent.futures.as_completed(futures):
            entry = futures[future]
            try:
                results.append(future.result())
            except BaseException as error:
                results.append({"id": entry["id"], "status": "fail", "error": str(error)})
            report()
    final = report(True)
    print(json.dumps({"status": final["status"], "completed": final["completed"], "total": final["total"], "elapsed_seconds": final["elapsed_seconds"], "scope": final["scope"]}), flush=True)
    return 0 if final["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
