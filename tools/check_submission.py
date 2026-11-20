#!/usr/bin/env python3
"""Offline structural preflight for this repository; never runs Lean or a kernel.

Official Palomar validators are pinned under palomar_contract. This wrapper
calls only their static functions. Compilation and Palomar verification are
reported separately and are never inferred from these checks.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
import re
import socket
import subprocess
import sys
import tempfile
import tomllib
import urllib.request
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CONTRACT = HERE / "palomar_contract"
sys.path.insert(0, str(CONTRACT))

def no_external_execution(*args: Any, **kwargs: Any) -> Any:
    raise RuntimeError("The static checker forbids network, subprocesses, builds and kernels")

# Fail closed if a future vendor import/static call tries external execution.
subprocess.run = no_external_execution
subprocess.Popen = no_external_execution
subprocess.call = no_external_execution
subprocess.check_call = no_external_execution
subprocess.check_output = no_external_execution
socket.create_connection = no_external_execution
socket.socket.connect = no_external_execution
socket.socket.connect_ex = no_external_execution
urllib.request.urlopen = no_external_execution
os.system = no_external_execution
os.popen = no_external_execution

try:
    from scripts import source_requirements as source_rules
    from scripts import submission_contract as metadata_rules
    from scripts import verify_submission as project_rules
    from scripts.verification_errors import FormalizationValidationError, VerificationError
except ModuleNotFoundError as error:
    raise SystemExit(
        "Static-check dependency unavailable: " + str(error)
        + ". Install the pinned PyYAML requirement in tools/palomar_contract/requirements.txt."
    )

# These orchestrators are deliberately inaccessible from the wrapper.
project_rules.prepare = no_external_execution
project_rules.execute = no_external_execution
project_rules.run = no_external_execution

EXPECTED_GROUPS = {
    "MF-05": ["MF-05", "MF-07"], "MF-12": ["MF-12"],
    "RA-02": ["RA-02", "RA-03"], "RA-08": ["RA-08"], "RA-09": ["RA-09"],
    "IE-21": ["IE-21"], "IE-22": ["IE-22"], "TR-04": ["TR-04"],
    "TR-27": ["TR-27"], "IS-03": ["IS-03"], "NM-04": ["NM-04"],
    "PF-02": ["PF-02"], "MD-06": ["MD-06"], "IV-04": ["IV-02", "IV-04"],
    "MI-19": ["MI-19"], "MI-21": ["MI-21"], "MI-22": ["MI-22"],
}
EXCLUDED_GENERATED_DIRECTORIES = {".git", ".lake", "__pycache__", ".build-cache"}


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest_file(filename: Path) -> str:
    return digest_bytes(filename.read_bytes())


def issue(error: Exception | str, *, stage: str, path: str | None = None) -> dict[str, Any]:
    value = {"stage": stage, "message": str(error)}
    for field in ("code", "field", "line", "column"):
        entry = getattr(error, field, None)
        if entry is not None:
            value[field] = entry
    if path is not None:
        value["path"] = path
    return value


def contained(root: Path, text: Any, *, directory: bool = False) -> Path:
    if not isinstance(text, str) or not text or "\\" in text or re.search(r"[?#\x00-\x1f\x7f]", text):
        raise ValueError("Expected a safe repository-relative path using forward slashes")
    parts = text.split("/")
    if any(part in {"", ".", ".."} for part in parts) or Path(text).is_absolute() or ":" in text:
        raise ValueError("Unsafe repository-relative path: " + text)
    candidate = root
    for part in parts:
        candidate = candidate / part
        if candidate.is_symlink():
            raise ValueError("Symlink component: " + text)
    candidate.resolve().relative_to(root.resolve())
    if directory and not candidate.is_dir():
        raise ValueError("Missing project directory: " + text)
    if not directory and not candidate.is_file():
        raise ValueError("Missing regular file: " + text)
    return candidate


def files_under(root: Path):
    for directory, subdirectories, filenames in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in EXCLUDED_GENERATED_DIRECTORIES
            and not (Path(directory) / name).is_symlink()
            and not (Path(directory) == root and name == "dist")
            and not (Path(directory) == root / "verification" and name == "local-builds")
        )
        for name in sorted(filenames):
            yield Path(directory) / name


def project_inventory(project: Path) -> tuple[str, list[dict[str, str]]]:
    """Hash exact build/config inputs, independently of metadata and generated output."""
    records = []
    for filename in files_under(project):
        if filename.is_symlink() or not filename.is_file():
            continue
        if filename.suffix == ".lean" or filename.name in {
            "lean-toolchain", "lake-manifest.json", "lakefile.toml", "comparator.json"
        }:
            records.append({"path": filename.relative_to(project).as_posix(), "sha256": digest_file(filename)})
    records.sort(key=lambda record: record["path"])
    serialized = json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    return digest_bytes(serialized), records


def selected_module_source(project: Path, module: str, lake: dict[str, Any]) -> Path:
    """Resolve the conventional committed source roots without executing Lake.

    Full authoritative Lake resolution remains a Palomar step. Non-default
    source roots are admitted only when explicit in the declarative Lakefile.
    """
    suffix = project_rules.module_source_suffix(module)
    source_roots = [str(lake.get("srcDir", "."))]
    for library in lake.get("lean_lib", []):
        if isinstance(library, dict):
            source_roots.append(str(library.get("srcDir", lake.get("srcDir", "."))))
    seen = set()
    for source_root in source_roots:
        if source_root in seen:
            continue
        seen.add(source_root)
        candidate = project / source_root / Path(*suffix.parts)
        try:
            candidate.resolve().relative_to(project.resolve())
        except ValueError:
            raise ValueError("Lake source directory escapes selected project")
        if candidate.is_file() and not candidate.is_symlink():
            return candidate
    raise ValueError("Named Lean module has no conventional committed source: " + module)


def direct_challenge_imports(filename: Path) -> list[str]:
    text = project_rules.strip_lean_comments(filename.read_text(encoding="utf-8"))
    imports = []
    for line in text.splitlines():
        match = re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+?)\s*$", line)
        if match:
            imports.extend(match.group(1).split())
    return imports



def selected_axiom_evidence(root: Path, entry: dict, build: dict) -> dict:
    """Validate retained public query evidence; native compiled files are not bundled."""
    base = "verification/selected-axioms/" + entry["id"]
    expected_path = base + "/selected-axioms.json"
    if build.get("selected_axioms_receipt") != expected_path:
        raise ValueError("Missing or unexpected selected-axiom receipt path")
    receipt_path = contained(root, expected_path)
    if digest_file(receipt_path) != build.get("selected_axioms_receipt_sha256"):
        raise ValueError("Selected-axiom receipt digest mismatch")
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    for key, value in {
        "schema_version": 1, "kind": "ordinary-compiled-solution-selected-axiom-query",
        "status": "pass", "selected_axioms_checked": True, "source_stable": True,
        "exit_code": 0, "errors": [], "kernel_replay_performed": False,
        "source_inventory_sha256": entry["source_inventory_sha256"],
        "project_root": entry["project_path"], "solution_module": entry["solution_module"],
        "theorem_names": entry["theorem_names"], "permitted_axioms": sorted(entry["permitted_axioms"]),
        "compiler_version": build["compiler_version"], "compiler_sha256": build["compiler_sha256"],
    }.items():
        if receipt.get(key) != value:
            raise ValueError("Selected-axiom receipt mismatch: " + key)
    if not re.fullmatch(r"[0-9a-f]{64}", receipt["compiler_sha256"]):
        raise ValueError("Invalid selected-axiom compiler digest")
    version = entry["toolchain"].removeprefix("leanprover/lean4:v")
    if not re.search(r"\bversion " + re.escape(version) + r"[, )]", receipt["compiler_version"]):
        raise ValueError("Selected-axiom compiler/toolchain mismatch")
    payloads = {}
    for role, filename in (("query", "query.txt"), ("stdout", "stdout.txt"), ("stderr", "stderr.txt")):
        expected = base + "/" + filename
        if receipt.get(role + "_path") != expected:
            raise ValueError("Unexpected selected-axiom public path: " + role)
        data = contained(root, expected).read_bytes()
        if digest_bytes(data) != receipt.get(role + "_sha256"):
            raise ValueError("Selected-axiom artifact digest mismatch: " + role)
        payloads[role] = data.decode("utf-8")
    for role in ("query", "stdout"):
        if build.get("selected_axioms_" + role + "_sha256") != receipt[role + "_sha256"]:
            raise ValueError("Build/selected-axiom artifact digest mismatch: " + role)
    expected_query = "module\n\nimport " + entry["solution_module"] + "\n\n" + "".join(
        "#print axioms " + name + "\n" for name in entry["theorem_names"]
    )
    if payloads["query"] != expected_query:
        raise ValueError("Selected-axiom query does not request exactly the configured declarations")
    parsed = {}
    pattern = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
    for match in pattern.finditer(payloads["stdout"]):
        if match[1] in parsed:
            raise ValueError("Duplicate theorem in selected-axiom output")
        parsed[match[1]] = [axiom.strip() for axiom in (match[2] or "").split(",") if axiom.strip()]
    if set(parsed) != set(entry["theorem_names"]) or parsed != receipt.get("axioms_by_theorem"):
        raise ValueError("Selected-axiom output does not match the reported configured declarations")
    if any(set(axioms) - set(entry["permitted_axioms"]) for axioms in parsed.values()):
        raise ValueError("Selected-axiom output contains forbidden axioms")
    artifacts = receipt.get("solution_artifacts", [])
    suffixes = [".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig"]
    module_path = entry["solution_module"].replace(".", "/")
    if len(artifacts) != len(suffixes):
        raise ValueError("Incomplete compiled Solution artifact record")
    for artifact, suffix in zip(artifacts, suffixes):
        if (not isinstance(artifact, dict) or not isinstance(artifact.get("path"), str)
            or not artifact["path"].replace("\\", "/").endswith("/" + module_path + suffix)
            or not re.fullmatch(r"[0-9a-f]{64}", str(artifact.get("sha256", "")))
            or type(artifact.get("bytes")) is not int or artifact["bytes"] <= 0):
            raise ValueError("Malformed compiled Solution artifact record")
    return {"receipt": expected_path, "receipt_sha256": digest_file(receipt_path),
            "public_artifacts_checked": True, "native_compiled_artifacts_available": False}


def check_set(root: Path, index_path: Path, build_report: Path | None = None, *, component_mode: bool = False) -> dict[str, Any]:
    expected_groups = EXPECTED_GROUPS if component_mode else {"NLA20": [problem for group in EXPECTED_GROUPS.values() for problem in group]}
    failures: list[dict[str, Any]] = []
    warnings: list[dict[str, Any]] = []
    report: dict[str, Any] = {
        "schema_version": 1,
        "checked_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "kind": "offline_static_submission_contract",
        "palomar_submission_commit": "14aa8d6b3c2f14a8540605e37144560b9a00e7e7",
        "static_contract_pass": False,
        "compatible_build_pass": False,
        "ready_for_submission": False,
        "palomar_verified": False,
        "kernel_replay_performed": False,
        "network_used": False,
        "projects": [],
        "failures": failures,
        "warnings": warnings,
        "limitations": [
            "This checks the intended source snapshot, excluding .git, .lake and Python bytecode directories.",
            "It does not execute Lake, compile Lean, resolve/fetch dependencies, inspect kernel exports or replay proofs.",
            "Direct Challenge imports and conventional declarative source paths are checked locally; Palomar reconstructs and authenticates the full transitive closure.",
            "Standard Apache text is compared to the pinned reference; Palomar separately runs its own licence detector.",
            "Palomar's future full mechanical verification, editorial review and rendering remain separate requirements.",
        ],
    }
    # Verify that the official static validators and data have not drifted.
    source_manifest = json.loads((CONTRACT / "SOURCE.json").read_text())
    for record in source_manifest["copied_files"] + source_manifest.get("additional_reference_files", []):
        filename = CONTRACT / record["path"]
        if not filename.is_file() or digest_file(filename) != record["sha256"]:
            failures.append(issue("Pinned official validator/data digest mismatch", stage="contract_integrity", path=record["path"]))

    source_scan, source_errors = source_rules.inspect_lean_sources(root)
    report["lean_source_scan"] = source_scan
    failures.extend(issue(error, stage="source_scan", path=getattr(error, "path", None)) for error in source_errors)
    intended_files = [p for p in files_under(root) if p.is_file() and not p.is_symlink()]
    report["intended_source_bytes"] = sum(p.stat().st_size for p in intended_files)
    if report["intended_source_bytes"] > project_rules.MAX_SOURCE_BYTES:
        failures.append(issue("Intended source checkout exceeds 500 MiB", stage="source_size"))
    for filename in intended_files:
        relative = filename.relative_to(root).as_posix()
        if filename.suffix in project_rules.COMPILED_ARTIFACT_SUFFIXES or any(
            filename.name.endswith(suffix) for suffix in project_rules.COMPILED_ARTIFACT_NAME_SUFFIXES
        ):
            failures.append(issue("Compiled artifact outside .lake", stage="artifact_scan", path=relative))
        with filename.open("rb") as stream:
            prefix = stream.read(128)
        if prefix.startswith(b"version https://git-lfs.github.com/spec/v1"):
            failures.append(issue("Git LFS pointer is not preservable source", stage="artifact_scan", path=relative))
    if (root / ".gitmodules").exists():
        failures.append(issue("Submission must not contain Git submodules", stage="artifact_scan", path=".gitmodules"))
    try:
        license_file = project_rules.repository_license_file(root)
        canonical = (CONTRACT / "data/Apache-2.0.txt").read_text(encoding="utf-8")
        actual = license_file.read_text(encoding="utf-8")
        if " ".join(actual.split()) != " ".join(canonical.split()):
            raise ValueError("Root licence does not exactly match the pinned standard Apache-2.0 text (ignoring whitespace)")
        report["license"] = {"path": license_file.name, "spdx": "Apache-2.0", "sha256": digest_file(license_file), "method": "pinned_standard_text_comparison"}
    except Exception as error:
        failures.append(issue(error, stage="root_license"))
    try:
        index = json.loads(index_path.read_text(encoding="utf-8"))
        rows = index if isinstance(index, list) else index.get("components" if component_mode else "entries", index.get("entries", index.get("projects")))
        if not isinstance(rows, list) or not rows:
            raise ValueError("Submission index must contain a nonempty entries/projects list")
    except Exception as error:
        failures.append(issue(error, stage="submission_index"))
        rows = []
    ids = [row.get("id") for row in rows if isinstance(row, dict)]
    if len(ids) != len(rows) or len(set(ids)) != len(ids) or set(ids) != set(expected_groups):
        failures.append(issue("Submission index must contain exactly the declared component groups" if component_mode else "Submission index must contain one root NLA20 entry", stage="submission_index"))
    for row in rows:
        if not isinstance(row, dict):
            failures.append(issue("Each submission-index row must be a mapping", stage="submission_index"))
            continue
        local_failures = []
        entry: dict[str, Any] = {"id": row.get("id"), "status": "fail", "failures": local_failures}
        report["projects"].append(entry)
        try:
            project_id = row["id"]
            if row.get("problem_ids") != expected_groups.get(project_id):
                raise ValueError("problem_ids must match the declared 20-problem grouping")
            entry["problem_ids"] = row["problem_ids"]
            project = root if not component_mode and row["project_path"] == "." else contained(root, row["project_path"], directory=True)
            entry["project_path"] = row["project_path"]
            source_digest, records = project_inventory(project)
            entry["source_inventory_sha256"] = source_digest
            entry["source_inventory_files"] = len(records)
            config_path = contained(root, row["comparator_config_path"])
            metadata_path = contained(root, row["formalization_metadata_path"])
            config_path.relative_to(project)
            if config_path.suffix != ".json" or metadata_path.name != "formalization.yaml":
                raise ValueError("Invalid Comparator or metadata filename")
            entry["project_path"] = row["project_path"]
            lakefiles = [project / n for n in ("lakefile.toml", "lakefile.lean") if (project / n).is_file()]
            if len(lakefiles) != 1 or lakefiles[0].is_symlink() or lakefiles[0].stat().st_size > project_rules.MAX_CONFIGURATION_BYTES:
                raise ValueError("Selected project needs exactly one regular Lakefile within 1 MiB")
            lake: dict[str, Any] = {}
            if lakefiles[0].suffix == ".toml":
                lake = tomllib.loads(lakefiles[0].read_text(encoding="utf-8"))
            else:
                raise ValueError("Offline local module resolution requires a declarative lakefile.toml; executable Lakefiles need an additional reviewed source-path adapter")
            manifest = project / "lake-manifest.json"
            if manifest.is_symlink() or not manifest.is_file():
                raise ValueError("Commit the selected project's Lake manifest")
            manifest_data = json.loads(manifest.read_text(encoding="utf-8"))
            if not isinstance(manifest_data, dict) or not isinstance(manifest_data.get("packages"), list):
                raise ValueError("Malformed committed Lake manifest")
            dependencies = project_rules.manifest_packages(project)
            project_rules.manifest_packages_directory(project, checkout=root)
            entry["dependencies"] = dependencies
            for package in manifest_data["packages"]:
                if package.get("type") not in {"git", "path"}:
                    raise ValueError("Unsupported package type in committed manifest")
                if package.get("type") == "path":
                    project_rules.contained_path_dependency(project, str(package.get("dir", "")), root, str(package.get("name", "")))
            toolchain_path = project / "lean-toolchain"
            if not toolchain_path.exists():
                toolchain_path = root / "lean-toolchain"
            toolchain = toolchain_path.read_text(encoding="utf-8").strip()
            project_rules.supported_toolchain(toolchain)
            entry["toolchain"] = toolchain
            # Bind canonical dependency/toolchain compatibility to fetched exact metadata.
            pinned_mathlib = "56a005855ea17e0b0958f73ec801ae140b0a1679"
            by_name = {item["name"]: item for item in dependencies}
            if by_name.get("mathlib", {}).get("repository", "").lower() != "leanprover-community/mathlib4":
                raise ValueError("Challenge Mathlib must come from its canonical repository")
            if by_name.get("mathlib", {}).get("revision") != pinned_mathlib:
                raise ValueError("Mathlib must match the researched stable Lean 4.35.0 commit; refresh recorded metadata before choosing another pin")
            expected_toolchain = (CONTRACT / "data/mathlib-4.35.0-lean-toolchain").read_text().strip()
            if toolchain != expected_toolchain:
                raise ValueError("Project toolchain does not match the exact canonical Mathlib source")
            canonical_manifest = json.loads((CONTRACT / "data/mathlib-4.35.0-lake-manifest.json").read_text())
            for package in canonical_manifest["packages"]:
                actual = by_name.get(metadata_rules.lake_package_name(package["name"]))
                if (not actual or actual["revision"] != package["rev"]
                    or actual["repository"].lower() != project_rules.github_repository(package["url"]).lower()):
                    raise ValueError("Dependency differs from canonical Mathlib manifest closure: " + package["name"])
            leancert = next((item for item in dependencies if item["name"].lower() == "leancert"), None)
            if leancert is not None:
                if leancert["repository"].lower() != "alerad/leancert":
                    raise ValueError("LeanCert must come from its recorded upstream repository")
                if leancert["revision"] != "2fde8a7b6f47da1a0ea1f52e2e93f16f3bf5de09":
                    raise ValueError("LeanCert differs from the researched matching stable Lean 4.35.0 revision")
                if toolchain != (CONTRACT / "data/leancert-4.35.0-lean-toolchain").read_text().strip():
                    raise ValueError("Project toolchain differs from the selected LeanCert source")
            metadata = metadata_rules.load_formalization_metadata(metadata_path)
            if metadata["project"]["license"] != "Apache-2.0":
                raise ValueError("Metadata licence must match the authorized root Apache-2.0 licence")
            config = project_rules.load_comparator_config(config_path)
            if config.get("definition_names", []):
                raise ValueError("This development does not permit intentional definition holes")
            entry["theorem_count"] = len(config["theorem_names"])
            entry["theorem_names"] = config["theorem_names"]
            entry["solution_module"] = config["solution_module"]
            entry["permitted_axioms"] = config["permitted_axioms"]
            entry["definition_holes"] = 0
            for role in ("challenge", "solution"):
                source = selected_module_source(project, config[role + "_module"], lake)
                entry[role + "_source"] = source.relative_to(root).as_posix()
                if role == "challenge":
                    text = source.read_text(encoding="utf-8")
                    size = source.stat().st_size
                    lines = source_rules.physical_lines(text)
                    entry["challenge_bytes"] = size
                    entry["challenge_lines"] = lines
                    if size > project_rules.MAX_CHALLENGE_BYTES or lines > project_rules.MAX_CHALLENGE_LINES:
                        raise ValueError("Selected Challenge exceeds 100 KiB or 1,000 lines")
                    if size > 32768 or lines > 300:
                        warnings.append(issue("Challenge exceeds recommended 32 KiB or 300 lines", stage="challenge_auditability", path=entry[role + "_source"]))
                    imports = direct_challenge_imports(source)
                    entry["challenge_direct_imports"] = imports
                    for imported in imports:
                        local = project / Path(*project_rules.module_source_suffix(imported).parts)
                        if local.is_file() or imported.split(".")[0] not in {"Mathlib", "Lean", "Init", "Std"}:
                            raise ValueError("Challenge imports a project/noncanonical source: " + imported)
            source_digest, records = project_inventory(project)
            entry["source_inventory_sha256"] = source_digest
            entry["source_inventory_files"] = len(records)
            entry["status"] = "pass"
        except FormalizationValidationError as error:
            for detail in error.issues:
                local_failures.append(issue(detail, stage="metadata", path=row.get("formalization_metadata_path")))
        except Exception as error:
            local_failures.append(issue(error, stage="project", path=row.get("project_path")))
        failures.extend({"project": entry["id"], **failure} for failure in local_failures)
    report["static_contract_pass"] = not failures
    if build_report is None:
        build_report = root / ("verification/build-status.json" if component_mode else "verification/combined-build-status.json")
    if build_report.is_file():
        try:
            builds = json.loads(build_report.read_text(encoding="utf-8"))
            by_id = {item["id"]: item for item in builds["projects"]}
            all_built = (builds.get("status") == "pass" and builds.get("kind") == ("ordinary-source-compilation" if component_mode else "ordinary-combined-source-compilation")
                         and len(builds["projects"]) == len(expected_groups))
            for entry in report["projects"]:
                build = by_id.get(entry["id"], {})
                matching = (
                    build.get("status") == "pass"
                    and build.get("all_project_modules_compiled" if component_mode else "combined_solution_compiled") is True
                    and (component_mode or build.get("combined_challenge_compiled") is True)
                    and build.get("selected_axioms_checked") is True
                    and build.get("source_inventory_sha256") == entry.get("source_inventory_sha256")
                    and build.get("toolchain") == entry.get("toolchain")
                )
                matching = matching and build.get("source_stable") is True and build.get("exit_code") == 0
                if matching:
                    try:
                        entry["selected_axiom_evidence"] = selected_axiom_evidence(root, entry, build)
                    except Exception as error:
                        matching = False
                        warnings.append(issue(error, stage="selected_axiom_evidence", path=entry["project_path"]))
                entry["compatible_build_pass"] = matching
                all_built = all_built and matching
            report["compatible_build_pass"] = all_built and len(by_id) == len(expected_groups)
            report["build_report"] = build_report.relative_to(root).as_posix()
        except Exception as error:
            warnings.append(issue(error, stage="build_evidence"))
    report["ready_for_submission"] = report["static_contract_pass"] and report["compatible_build_pass"]
    report["status"] = "READY" if report["ready_for_submission"] else (
        "BUILD_NOT_VERIFIED" if report["static_contract_pass"] else "FAIL"
    )
    return report





def supporting_theorems(root: Path) -> list[dict]:
    filename = root / "audit/combined-supporting-theorems.json"
    if not filename.exists():
        return []
    data = json.loads(filename.read_text(encoding="utf-8"))
    rows = data.get("theorems") if isinstance(data, dict) and data.get("schema_version") == 1 else None
    if not isinstance(rows, list):
        raise ValueError("Malformed technical supporting-theorem manifest")
    names = []
    problems = {problem for group in EXPECTED_GROUPS.values() for problem in group}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("Each technical supporting theorem needs an account")
        for key in ("name", "type_lean", "source_path", "source_module", "purpose"):
            if not isinstance(row.get(key), str) or not row[key].strip():
                raise ValueError("Missing supporting-theorem field: " + key)
        if row["name"].startswith("_private.") or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", row["name"]):
            raise ValueError("Supporting theorem needs a stable public Lean name")
        if contained(root, row["source_path"]).suffix != ".lean":
            raise ValueError("Supporting theorem source must be a retained Lean file")
        if not isinstance(row.get("problem_ids"), list) or not row["problem_ids"] or not set(row["problem_ids"]) <= problems:
            raise ValueError("Supporting theorem needs valid source problem IDs")
        names.append(row["name"])
    if len(set(names)) != len(names):
        raise ValueError("Duplicate technical supporting theorem")
    return rows

def compiled_artifact_hashes(records: Any, module: str) -> dict[str, str]:
    suffixes = [".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig"]
    if not isinstance(records, list) or len(records) != len(suffixes):
        raise ValueError("Expected all five compiled module artifacts")
    base = "/" + module.replace(".", "/")
    result = {}
    for record in records:
        if not isinstance(record, dict):
            raise ValueError("Malformed compiled artifact record")
        name = str(record.get("path", "")).replace("\\", "/")
        matches = [suffix for suffix in suffixes if name.endswith(base + suffix)]
        if len(matches) != 1 or matches[0] in result:
            raise ValueError("Unexpected or duplicate compiled artifact path")
        digest = record.get("sha256", "")
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError("Invalid compiled artifact digest")
        result[matches[0]] = digest
    if set(result) != set(suffixes):
        raise ValueError("Incomplete compiled module artifact set")
    return result


def statement_correspondence_evidence(root: Path, entry: dict, build_report: Path) -> dict:
    """Bind local comparison-core results to this build and current sources."""
    filename = contained(root, "verification/combined-correspondence.json")
    receipt = json.loads(filename.read_text(encoding="utf-8"))
    config_path = contained(root, "comparator.json")
    config = project_rules.load_comparator_config(config_path)
    builds = json.loads(build_report.read_text(encoding="utf-8"))
    rows = [row for row in builds.get("projects", []) if row.get("id") == "NLA20"]
    if len(rows) != 1:
        raise ValueError("Missing unique combined build row for comparison binding")
    build = rows[0]
    for key, expected in {
        "schema_version": 1, "kind": "lean-bundled-comparator-core", "status": "pass",
        "comparison_passed": True, "source_inventory_sha256": entry["source_inventory_sha256"],
        "challenge_module": config["challenge_module"], "solution_module": config["solution_module"],
        "theorem_names": config["theorem_names"], "definition_names": config.get("definition_names", []),
        "comparator_config_sha256": digest_file(config_path), "kernel_replay_performed": False,
        "compiler_version": build["compiler_version"], "compiler_sha256": build["compiler_sha256"],
        "permitted_axioms": config["permitted_axioms"], "source_stable": True, "exit_code": 0,
        "proof_export_performed": False, "nanoda_replay_performed": False,
        "official_palomar_verification": False, "compiled_artifacts_stable": True, "driver_stable": True,
        "phase_exit_codes": [0, 0, 0], "statement_materialization_performed": True,
        "selected_proof_values_omitted": True, "lake_library_stable": True,
        "selected_declarations_are_theorems": True, "query_stable": True, "compiler_stable": True,
        "native_toolchain_inputs_stable": True, "native_executable_stable": True,
        "generated_c_stable": True, "statement_materializations_stable": True,
        "native_compile_steps": [{"stage": "emit-c", "exit_code": 0}, {"stage": "link-native", "exit_code": 0}],
        "expression_normalization": ["erase_expr_mdata", "normalize_let_nondep_false"],
    }.items():
        if receipt.get(key) != expected:
            raise ValueError("Comparison-core receipt mismatch: " + key)
    library_digest = receipt.get("lake_library_sha256", "")
    library_name = str(receipt.get("lake_library_path", "")).replace(chr(92), "/").rsplit("/", 1)[-1]
    if not isinstance(library_digest, str) or not re.fullmatch(r"[0-9a-f]{64}", library_digest) or library_name not in {"libLake.a", "libLake_shared.dll", "libLake_shared.so", "libLake_shared.dylib"}:
        raise ValueError("Missing or malformed bundled Lake comparison-library record")
    native = receipt.get("native_toolchain_inputs")
    required_native = {"leanc": {"leanc", "leanc.exe"}, "clang": {"clang", "clang.exe"},
                       "lake_static_library": {"libLake.a"}, "export_static_library": {"libLeanExport.a"}}
    if not isinstance(native, dict) or not set(required_native) <= set(native):
        raise ValueError("Missing native comparison toolchain input records")
    for role, record in native.items():
        if not isinstance(record, dict) or not re.fullmatch(r"[0-9a-f]{64}", str(record.get("sha256", ""))):
            raise ValueError("Malformed native comparison input digest: " + role)
        basename = str(record.get("path", "")).replace(chr(92), "/").rsplit("/", 1)[-1]
        if not basename or (role in required_native and basename not in required_native[role]):
            raise ValueError("Unexpected native comparison input path: " + role)
    if native["lake_static_library"]["sha256"] != library_digest:
        raise ValueError("Native Lake library digest differs from the comparison library record")
    for key in ("native_executable_sha256", "generated_c_sha256"):
        if not re.fullmatch(r"[0-9a-f]{64}", str(receipt.get(key, ""))):
            raise ValueError("Missing native comparison product digest: " + key)
    materializations = receipt.get("statement_materializations")
    if not isinstance(materializations, list) or [item.get("module") for item in materializations if isinstance(item, dict)] != [config["challenge_module"], config["solution_module"]]:
        raise ValueError("Both independent statement maps must be materialized in order")
    for item in materializations:
        if not re.fullmatch(r"[0-9a-f]{64}", str(item.get("sha256", ""))) or type(item.get("bytes")) is not int or item["bytes"] <= 0:
            raise ValueError("Malformed statement materialization record")
    details = receipt.get("details")
    if not isinstance(details, dict) or details.get("compared_theorems") != len(config["theorem_names"]) or details.get("type_negative_control") is not True or details.get("definition_body_negative_control") is not True:
        raise ValueError("Both comparison negative controls and the exact selected count must pass")
    driver_path = contained(root, receipt.get("driver_path"))
    if driver_path.suffix != ".py" or not driver_path.relative_to(root).as_posix().startswith("scripts/"):
        raise ValueError("Unexpected comparison driver path")
    if digest_file(driver_path) != receipt.get("driver_sha256"):
        raise ValueError("Comparison driver changed since the correspondence check")
    for role in ("query", "stdout", "stderr"):
        expected_path = "verification/correspondence/" + role + ".txt"
        if receipt.get(role + "_path") != expected_path:
            raise ValueError("Unexpected comparison artifact path: " + role)
        if digest_file(contained(root, expected_path)) != receipt.get(role + "_sha256"):
            raise ValueError("Comparison artifact digest mismatch: " + role)
    axiom = json.loads(contained(root, "verification/selected-axioms/NLA20/selected-axioms.json").read_text(encoding="utf-8"))
    for role in ("challenge", "solution"):
        actual = compiled_artifact_hashes(receipt.get(role + "_artifacts"), config[role + "_module"])
        expected = compiled_artifact_hashes(build.get(role + "_artifacts"), config[role + "_module"])
        if actual != expected:
            raise ValueError("Correspondence check used different compiled " + role + " artifacts")
        if role == "solution" and actual != compiled_artifact_hashes(axiom.get("solution_artifacts"), config["solution_module"]):
            raise ValueError("Correspondence and axiom query used different compiled Solutions")
    return {"path": filename.relative_to(root).as_posix(), "sha256": digest_file(filename),
            "statement_types_and_fixed_definitions_compared": True, "kernel_replay_performed": False}

def check(root: Path, index_path: Path, build_report: Path | None = None) -> dict[str, Any]:
    """One submitted root project, with separately retained component evidence."""
    components = check_set(root, index_path, component_mode=True)
    report = check_set(root, index_path, build_report)
    report["submission_count"] = 1
    report["components"] = components["projects"]
    report["component_count"] = len(components["projects"])
    report["component_build_pass"] = components["compatible_build_pass"]
    report["combined_build_pass"] = report["compatible_build_pass"]
    report["component_build_report"] = components.get("build_report")
    report["failures"].extend({"scope": "component", **item} for item in components["failures"])
    report["warnings"].extend({"scope": "component", **item} for item in components["warnings"])
    try:
        index = json.loads(index_path.read_text(encoding="utf-8"))
        if index.get("submission_count") != 1 or len(index.get("entries", [])) != 1:
            raise ValueError("Exactly one Palomar submission must be declared")
        row = index["entries"][0]
        if row.get("project_path") != "." or row.get("comparator_config_path") != "comparator.json" or row.get("formalization_metadata_path") != "formalization.yaml":
            raise ValueError("The single submitted project and files must be at repository root")
        base = [name for component in components["projects"] for name in component.get("theorem_names", [])]
        technical = supporting_theorems(root)
        expected = base + [item["name"] for item in technical]
        actual = report["projects"][0].get("theorem_names", []) if report["projects"] else []
        if len(set(base)) != len(base) or len(base) != 34:
            raise ValueError("The component selections must identify exactly 34 distinct base declarations")
        if len(set(expected)) != len(expected):
            raise ValueError("Technical helpers must not duplicate the base or each other")
        if actual != expected or row.get("selected_theorem_names") != expected:
            raise ValueError("Root Comparator must select the 34 base declarations followed by its documented technical theorems")
        report["base_selected_declarations"] = len(base)
        report["technical_supporting_theorems"] = technical
        report["selected_declarations"] = len(expected)
    except Exception as error:
        report["failures"].append(issue(error, stage="single_submission_scope"))
    report["challenge_source_anchors_pass"] = False
    try:
        anchor_script = root / "scripts/check_challenge_anchors.py"
        spec = importlib.util.spec_from_file_location("nla_challenge_anchor_check", anchor_script)
        if spec is None or spec.loader is None:
            raise ValueError("Cannot load the Challenge source-anchor validator")
        anchor_module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = anchor_module
        spec.loader.exec_module(anchor_module)
        report["challenge_source_anchors"] = anchor_module.validate_evidence(root)
        report["challenge_source_anchors_pass"] = True
    except Exception as error:
        report["failures"].append(issue(error, stage="challenge_source_anchors"))
    report["static_contract_pass"] = not report["failures"]
    report["compatible_build_pass"] = report["combined_build_pass"] and report["component_build_pass"]
    report["statement_correspondence_pass"] = False
    if report["combined_build_pass"]:
        try:
            combined_report = build_report if build_report is not None else root / "verification/combined-build-status.json"
            report["statement_correspondence"] = statement_correspondence_evidence(root, report["projects"][0], combined_report)
            report["statement_correspondence_pass"] = True
        except Exception as error:
            report["warnings"].append(issue(error, stage="statement_correspondence"))
    report["ready_for_submission"] = report["static_contract_pass"] and report["compatible_build_pass"] and report["statement_correspondence_pass"] and report["challenge_source_anchors_pass"]
    report["status"] = "READY" if report["ready_for_submission"] else (
        "FAIL" if not report["static_contract_pass"] else (
            "BUILD_NOT_VERIFIED" if not report["compatible_build_pass"] else "COMPARISON_NOT_VERIFIED"
        )
    )
    report["limitations"].append("The retained seventeen component receipts do not certify the combined Solution. A separate source-bound combined build, selected-axiom receipt, exact type/fixed-definition comparison-core report and compiler-backed source-anchor eligibility receipt are mandatory. The local comparison does not perform full proof export or kernel replay.")
    return report

def self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="palomar-static-negative-controls-") as directory:
        root = Path(directory)
        config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["Example.result"], "permitted_axioms": ["propext"], "definition_names": []}
        target = root / "comparator.json"
        target.write_text(json.dumps(config), encoding="utf-8")
        project_rules.load_comparator_config(target)
        for change in ({"fixed_definition_names": []}, {"permitted_axioms": ["sorryAx"]}, {"theorem_names": []}):
            target.write_text(json.dumps({**config, **change}), encoding="utf-8")
            try:
                project_rules.load_comparator_config(target)
            except VerificationError:
                pass
            else:
                raise AssertionError("Official config validator accepted a negative control: " + repr(change))
        assert not source_rules.source_issues("module\npublic theorem x : True := by trivial\n", "Good.lean")
        assert source_rules.source_issues("import Mathlib\n", "MissingModule.lean")
        assert source_rules.source_issues("module\n" + "\n" * 10000, "TooLong.lean")
        try:
            socket.create_connection(("example.com", 443))
        except RuntimeError:
            pass
        else:
            raise AssertionError("Network guard did not reject connection")
    print("Static checker negative controls passed; no build, kernel or network was run.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=HERE.parent)
    parser.add_argument("--index", type=Path, default=Path("submission-index.json"))
    parser.add_argument("--json", type=Path, help="Write detailed report to this file, relative to repository root unless absolute")
    parser.add_argument("--build-report", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--static-only", action="store_true", help="Use structural pass/fail for the exit code; readiness fields remain unchanged")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    root = args.root.resolve()
    index = args.index if args.index.is_absolute() else root / args.index
    build = args.build_report
    if build is not None and not build.is_absolute():
        build = root / build
    report = check(root, index, build)
    if args.json:
        target = args.json if args.json.is_absolute() else root / args.json
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in ("status", "static_contract_pass", "compatible_build_pass", "statement_correspondence_pass", "challenge_source_anchors_pass", "ready_for_submission", "palomar_verified", "kernel_replay_performed")}))
    for failure in report["failures"]:
        print("FAIL " + json.dumps(failure, ensure_ascii=False))
    for warning in report["warnings"]:
        print("WARN " + json.dumps(warning, ensure_ascii=False))
    if args.static_only:
        return 0 if report["static_contract_pass"] else 1
    return 0 if report["ready_for_submission"] else (2 if report["static_contract_pass"] else 1)


if __name__ == "__main__":
    raise SystemExit(main())
