"""Ordinary, serial Lean compilation in an isolated temporary working copy.
This does not run Comparator, NanoDa, or a kernel replay/export pipeline.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('id');p.add_argument('--lean',required=True,type=Path);p.add_argument('--cache-dir',type=Path,default=Path(tempfile.gettempdir())/'nla-palomar-deps-4.35.0');p.add_argument('--work-dir',type=Path,default=Path(tempfile.gettempdir())/'nla-palomar-build-4.35.0');p.add_argument('--memory-mb',type=int,default=6144);a=p.parse_args()
index=json.loads((ROOT/'submission-index.json').read_text(encoding='utf-8'))
entry=next(e for e in index.get('components', index['entries']) if e['id']==a.id)
source=(ROOT/entry['project_path']).resolve();assert source.is_relative_to(ROOT.resolve())
expected=(source/'lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
compiler_version=subprocess.check_output([str(a.lean.resolve()),'--version'],text=True).strip()
actual=re.search(r'\bversion\s+([^,\s)]+)',compiler_version)
if not actual or actual[1]!=expected:
 raise SystemExit('Compiler/toolchain mismatch: '+compiler_version+'; required '+expected)
work_base=a.work_dir.resolve();work=work_base/a.id
assert work.resolve().is_relative_to(work_base)
work.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def inventory():
 records=[]
 for d,dirs,files in os.walk(source,followlinks=False):
  dirs[:]=sorted(v for v in dirs if v not in {'.git','.lake','__pycache__'})
  for n in files:
   f=Path(d)/n;rel=f.relative_to(source).as_posix()
   if n.endswith('.lean') or rel in {'lean-toolchain','lake-manifest.json','lakefile.toml','comparator.json'}:
    assert not f.is_symlink()
    records.append(dict(path=rel,sha256=sha(f.read_bytes())))
 records.sort(key=lambda r:r['path'])
 return records,sha(json.dumps(records,sort_keys=True,separators=(',',':')).encode())
records,digest=inventory();prior_path=work/'.copied-source-inputs.json'
prior=json.loads(prior_path.read_text(encoding='utf-8')) if prior_path.exists() else []
names={r['path'] for r in records}
for old in prior:
 if old['path'] not in names:
  f=work/old['path'];assert f.resolve().is_relative_to(work.resolve())
  if f.is_file(): f.unlink()
for row in records:
 dest=work/row['path'];dest.parent.mkdir(parents=True,exist_ok=True);data=(source/row['path']).read_bytes()
 if not dest.exists() or dest.read_bytes()!=data: dest.write_bytes(data)
prior_path.write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
packages=(a.cache_dir/'.lake/packages').resolve();assert packages.is_dir()
link=work/'.lake/packages';link.parent.mkdir(parents=True,exist_ok=True)
if link.exists(): assert link.resolve()==packages
else:
 try: os.symlink(packages,link,target_is_directory=True)
 except OSError:
  assert os.name=='nt'
  env=dict(os.environ);env['NLA_BUILD_PACKAGES']=str(link);env['NLA_SOURCE_PACKAGES']=str(packages)
  subprocess.run(['powershell.exe','-NoProfile','-NonInteractive','-Command','New-Item -ItemType Junction -Path $env:NLA_BUILD_PACKAGES -Target $env:NLA_SOURCE_PACKAGES | Out-Null'],env=env,check=True)
log_dir=ROOT/'verification/local-builds';log_dir.mkdir(parents=True,exist_ok=True)
log=log_dir/(a.id+'.log')
command=[sys.executable,str(ROOT/'scripts/serial_build.py'),str(work),'--all-local','--lean',str(a.lean.resolve()),'--log',str(log),'--memory-mb',str(a.memory_mb),'--resume']
started=time.time();result=subprocess.run(command,cwd=ROOT)
after,after_digest=inventory();stable=after_digest==digest
axiom_result=None;axiom_error=None
if result.returncode==0 and stable:
 try:
  sys.path.insert(0,str(ROOT/'scripts'))
  from audit_selected_axioms import audit_project
  axiom_work=work_base.parent/(work_base.name+'-selected-axioms')/a.id
  lean_paths=[work/'.lake/build/lib/lean']+[v/'.lake/build/lib/lean' for v in sorted(packages.iterdir()) if v.is_dir()]
  axiom_result=audit_project(project_root=work,lean=a.lean,lean_path=os.pathsep.join(map(str,lean_paths)),work_dir=axiom_work,expected_source_inventory_sha256=digest)
  public=ROOT/'verification/selected-axioms'/a.id;public.mkdir(parents=True,exist_ok=True)
  for old,new in [('SelectedAxiomQuery.lean','query.txt'),('stdout.log','stdout.txt'),('stderr.log','stderr.txt')]:
   shutil.copyfile(axiom_work/old,public/new)
  axiom_result['native_paths']={key:axiom_result[key] for key in ('project_root','query_path','stdout_path','stderr_path')}
  axiom_result['project_root']=entry['project_path']
  for key,name in [('query_path','query.txt'),('stdout_path','stdout.txt'),('stderr_path','stderr.txt')]:
   axiom_result[key]=(public/name).relative_to(ROOT).as_posix()
  (public/'selected-axioms.json').write_text(json.dumps(axiom_result,indent=2)+'\n',encoding='utf-8')
 except Exception as error:
  axiom_error=repr(error)
selected_checked=bool(axiom_result and not axiom_error and axiom_result.get('selected_axioms_checked'))
report_path=ROOT/'verification/build-status.json'
report=json.loads(report_path.read_text(encoding='utf-8')) if report_path.exists() else dict(status='in-progress',kind='ordinary-source-compilation',kernel_replay_performed=False,projects=[])
report['projects']=[r for r in report['projects'] if r['id']!=a.id]
row=dict(id=a.id,status='pass' if result.returncode==0 and stable and selected_checked else 'fail',toolchain=(source/'lean-toolchain').read_text().strip(),source_inventory_sha256=digest,compiler_version=compiler_version,compiler_sha256=sha(a.lean.read_bytes()),all_project_modules_compiled=(result.returncode==0 and stable),selected_axioms_checked=selected_checked,selected_axioms_receipt='verification/selected-axioms/'+a.id+'/selected-axioms.json' if axiom_result else None,selected_axioms_receipt_sha256=sha((ROOT/'verification/selected-axioms'/a.id/'selected-axioms.json').read_bytes()) if axiom_result and not axiom_error else None,selected_axioms_query_sha256=axiom_result.get('query_sha256') if axiom_result else None,selected_axioms_stdout_sha256=axiom_result.get('stdout_sha256') if axiom_result else None,kernel_replay_performed=False,selected_axiom_error=axiom_error,source_stable=stable,exit_code=result.returncode,elapsed_seconds=time.time()-started,command=command,work_dir=str(work),log='verification/local-builds/'+log.name)
report['projects'].append(row)
report['status']='pass' if len(report['projects'])==len(index.get('components', index['entries'])) and all(r['status']=='pass' for r in report['projects']) else 'in-progress'
report_path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(row),flush=True)
raise SystemExit(0 if row['status']=='pass' else 1)
