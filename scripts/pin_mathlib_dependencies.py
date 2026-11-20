"""Regenerate all project build inputs from the canonical dependency profile.

This helper is for maintainers rebuilding staged sources. It does not fetch
dependencies, modify proof sources, or run a verification service.
"""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
profile=json.loads((ROOT/"dependency-profile.json").read_text(encoding="utf-8"))
assert profile["toolchain"]=="leanprover/lean4:v4.35.0"
assert profile["mathlib_revision"]=="56a005855ea17e0b0958f73ec801ae140b0a1679"
assert len(profile["packages"])==9
index=json.loads((ROOT/"submission-index.json").read_text(encoding="utf-8"))
for entry in index.get("components", index["entries"]):
    project=ROOT/entry["project_path"]
    name="nla_"+entry["id"].lower().replace("-","_")
    manifest=dict(version="1.2.0",packagesDir=".lake/packages",packages=profile["packages"],
        name=name,lakeDir=".lake",fixedToolchain=False)
    (project/"lean-toolchain").write_text(profile["toolchain"]+"\n",encoding="utf-8")
    (project/"lake-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    libraries={"Challenge","Solution"}
    for f in project.rglob("*.lean"):
        rel=f.relative_to(project)
        if any(p in {".lake",".git","__pycache__"} for p in rel.parts):continue
        libraries.add(rel.parts[0] if len(rel.parts)>1 else f.stem)
    toml='name = '+json.dumps(name)+'\nversion = "1.0.0"\ndefaultTargets = ["Solution"]\n\n'
    toml+='[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = '+json.dumps(profile["mathlib_revision"])+'\n'
    for lib in sorted(libraries):
        toml+='\n[[lean_lib]]\nname = '+json.dumps(lib)+'\nprecompileModules = false\n'
    (project/"lakefile.toml").write_text(toml,encoding="utf-8")
print("Regenerated all 17 toolchain, Lake and manifest files from canonical pins.")
