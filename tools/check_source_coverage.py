"""Check portable source coverage and refuse missing proofs or trust shortcuts.

This is a static source check. It does not replace Lean/Comparator/NanoDa.
"""
from pathlib import Path
import hashlib,json,re,sys,tarfile
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from lean_source import lean_code_mask
from serial_build import module_imports
index=json.loads((ROOT/"submission-index.json").read_text())
manifest=json.loads((ROOT/"audit/source-input-manifest.json").read_text())
archive=ROOT/manifest["archive"]
assert hashlib.sha256(archive.read_bytes()).hexdigest()==manifest["archive_sha256"]
with tarfile.open(archive) as t:
    named=json.load(t.extractfile("metadata/statement-coverage.json"))["statements"]
    prose=json.load(t.extractfile("metadata/additional-claims.json"))["claims"]
projects={e["id"]:ROOT/e["project_path"] for e in index.get("components", index["entries"])}
closures={};solution_closures={}
for pid,project in projects.items():
    seen=set()
    def visit(name):
        if name in seen:return
        seen.add(name)
        path=project/Path(*name.split(".")).with_suffix(".lean")
        if path.is_file():
            for imp in module_imports(path.read_text(encoding="utf-8-sig")):visit(imp)
    visit("Solution")
    solution_closures[pid]=set(seen)
    for source in project.rglob("*.lean"):
        if any(p in {".git",".lake","__pycache__",".build-cache"} for p in source.relative_to(project).parts):continue
        visit(".".join(source.relative_to(project).with_suffix("").parts))
    closures[pid]=seen
rows=[]; failures=[]
for kind,items in [("named",named),("prose",prose)]:
    for row in items:
        old=Path(row["proof_file"])
        assert old.parts[0]=="problems",str(old)
        pid=old.parts[1]
        relative=Path(*old.parts[2:])
        module=".".join(relative.with_suffix("").parts)
        present=(projects[pid]/relative).is_file() and module in closures[pid]
        if not present:failures.append(row["label"]+": proof source is not reachable")
        rows.append(dict(kind=kind,label=row["label"],project=pid,
            proof_file=(Path("projects")/pid/relative).as_posix(),
            lean_declarations=row["lean_declarations"],source_reachable=present,solution_reachable=module in solution_closures[pid]))
for pid,project in projects.items():
    for f in sorted(project.rglob("*.lean")):
        if ".lake" in f.parts:continue
        code=lean_code_mask(f.read_text(encoding="utf-8-sig"))
        banned=r"\b(?:axiom|native_decide|admit|Lean\.ofReduceBool)\b"
        if f.name!="Challenge.lean":banned=r"\b(?:sorry|axiom|native_decide|admit|Lean\.ofReduceBool)\b"
        for m in re.finditer(banned,code):
            failures.append(f.relative_to(ROOT).as_posix()+": forbidden token "+m[0])
out=dict(schema_version=1,status="pass" if not failures else "fail",
    scope="Static reachability in the independently compiled module graph and forbidden-token check; auxiliary alternative proof environments need not share one Solution import closure; no fresh kernel or statement-equivalence claim",
    manuscript_sha256=index["manuscript_sha256"],
    named_statement_count=len(named),prose_claim_group_count=len(prose),
    problem_count=index["resolved_problem_count"],projects=len(projects),
    claims=rows,failures=failures)
target=ROOT/"audit/source-coverage-check.json"
target.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
print(json.dumps({k:out[k] for k in ("status","named_statement_count","prose_claim_group_count","problem_count","projects")}))
for failure in failures:print("FAIL",failure)
raise SystemExit(1 if failures else 0)
