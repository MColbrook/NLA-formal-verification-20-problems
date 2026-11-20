"""Merge ordinary-build receipts; never run a replay."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument("directory",type=Path);p.add_argument("--output",type=Path,default=Path("verification/build-status.json"));a=p.parse_args()
root=Path(__file__).resolve().parents[1]
expected={e["id"] for e in (lambda index: index.get("components", index["entries"]))(json.loads((root/"submission-index.json").read_text()))}
rows={}
for f in sorted(a.directory.rglob("build-status.json")):
    data=json.loads(f.read_text())
    assert data.get("kind")=="ordinary-source-compilation" and data.get("kernel_replay_performed") is False,str(f)
    for row in data["projects"]:
        assert row["id"] in expected,str(f)
        assert row["status"]=="pass" and row["exit_code"]==0 and row["source_stable"] is True and row.get("all_project_modules_compiled") is True and row.get("selected_axioms_checked") is True,str(f)
        assert row["id"] not in rows,"Duplicate evidence: "+row["id"]
        receipt_path='verification/selected-axioms/'+row['id']+'/selected-axioms.json'
        assert row.get('selected_axioms_receipt')==receipt_path,'Missing public selected-axiom receipt'
        source=f.parent/'selected-axioms'/row['id']
        receipt=source/'selected-axioms.json'
        assert hashlib.sha256(receipt.read_bytes()).hexdigest()==row.get('selected_axioms_receipt_sha256'),'Selected-axiom receipt digest mismatch'
        data=json.loads(receipt.read_text(encoding='utf-8'))
        assert data.get('source_inventory_sha256')==row['source_inventory_sha256'] and data.get('selected_axioms_checked') is True,'Selected-axiom receipt/source mismatch'
        payloads={'selected-axioms.json':receipt.read_bytes()}
        for role,name in [('query','query.txt'),('stdout','stdout.txt'),('stderr','stderr.txt')]:
            assert data.get(role+'_path')=='verification/selected-axioms/'+row['id']+'/'+name,'Unexpected public selected-axiom path'
            payload=(source/name).read_bytes()
            assert hashlib.sha256(payload).hexdigest()==data.get(role+'_sha256'),'Selected-axiom artifact digest mismatch'
            payloads[name]=payload
        rows[row["id"]]=(row,payloads)
assert set(rows)==expected,"Missing projects: "+repr(sorted(expected-set(rows)))
out=dict(status="pass",kind="ordinary-source-compilation",kernel_replay_performed=False,projects=[rows[k][0] for k in sorted(rows)])
for project_id,(_,payloads) in sorted(rows.items()):
    destination=root/'verification/selected-axioms'/project_id
    destination.mkdir(parents=True,exist_ok=True)
    for name,payload in payloads.items():
        (destination/name).write_bytes(payload)
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
print("Merged 17 ordinary-build receipts; no Comparator or independent replay was run.")
