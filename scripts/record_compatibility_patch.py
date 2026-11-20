#!/usr/bin/env python3
"""Record hand-reviewed compatibility edits as reproducible literal patches.

The target files must already contain the intended reviewed edits. Their prior
bytes are reconstructed from the canonical source archive, visibility promotion,
and existing compatibility patches. No proof source is modified by this helper.

Example:
  python scripts/record_compatibility_patch.py --id mi21-sqrt-api \
    --reason "Use the Lean 4.35 square-root API; theorem statements unchanged" \
    --paths projects/MI-21/NLA/MI21/Proof.lean
  python scripts/stage_sources.py stage
  python scripts/stage_sources.py verify
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re

from stage_sources import ROOT, read_archive, promote, apply_compatibility_patches, checked_path, sha256, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--id", required=True)
    parser.add_argument("--reason", required=True)
    parser.add_argument("--paths", nargs="+", required=True)
    parser.add_argument("--statement-changes", action="store_true", help="Explicitly declare that mathematical statement text changed; review correspondence separately")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.id):
        parser.error("Patch id must use only letters, digits, underscores, and hyphens")
    manifest, archived = read_archive()
    lean_paths = {x["archive_path"] for x in manifest["inputs"] if x["kind"] == "lean-source"}
    records = []
    for name in dict.fromkeys(args.paths):
        checked_path(name)
        if name not in lean_paths:
            parser.error(f"Not an archived proof-source path: {name}; entry interfaces require their own generator/override records")
        promoted, _ = promote(archived[name])
        expected, _ = apply_compatibility_patches(name, promoted)
        actual = (ROOT / Path(name)).read_bytes()
        if actual == expected:
            continue
        # One exact whole-file replacement avoids guessed diff context. Both
        # complete states and their SHA256 identities are retained for review.
        records.append({"path": name, "before_sha256": sha256(expected), "after_sha256": sha256(actual), "edits": [{"old": expected.decode("utf-8"), "new": actual.decode("utf-8"), "occurrences": 1, "reason": args.reason}]})
    if not records:
        parser.error("No unrecorded changes were found in the supplied paths")
    folder = ROOT / "patches" / "compatibility"
    existing = sorted(folder.glob("*.json"))
    numbers = [int(m.group(1)) for f in existing if (m := re.match(r"zz(\d+)-", f.name))]
    sequence = max(numbers, default=0) + 1
    target = folder / f"zz{sequence:04d}-{args.id}.json"
    if existing and target.name <= existing[-1].name:
        parser.error("Cannot safely append to compatibility patch order; inspect existing patch filenames")
    patch = {"schema_version": 1, "id": args.id, "purpose": args.reason, "source": "Hand-reviewed edits recorded from current proof-source copies; this helper does not infer mathematical equivalence", "mathematical_statement_changes": args.statement_changes, "proof_or_api_change_description": args.reason, "records": records}
    write_json(target, patch)
    print(f"Recorded {len(records)} proof-source override(s) in {target.relative_to(ROOT)}")
    print("Run stage_sources.py stage, then stage_sources.py verify, to refresh the bound source manifest.")


if __name__ == "__main__":
    main()
