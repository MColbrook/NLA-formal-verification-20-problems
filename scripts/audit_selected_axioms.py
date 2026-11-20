#!/usr/bin/env python3
"""Query selected theorem axiom closures in compiled Solutions using ordinary Lean.

The query contains an import and #print axioms commands only. It performs no
Comparator run, proof export, NanoDa or independent kernel replay. The caller
must first complete a source-bound ordinary build of every local module.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path
from parallel_build import inventory

STANDARD_AXIOMS={'propext','Classical.choice','Quot.sound'}
COMMIT='eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
def sha(data):return hashlib.sha256(data).hexdigest()
def audit_project(*,project_root:Path,lean:Path,lean_path:str,work_dir:Path,expected_source_inventory_sha256:str,config_path:Path|None=None,timeout:int=300)->dict:
 project=Path(project_root).resolve();compiler=Path(lean).resolve();work=Path(work_dir).resolve();config_file=Path(config_path).resolve() if config_path else project/'comparator.json'
 if work==project or work.is_relative_to(project):raise ValueError('Query work directory must be outside project source inputs')
 work.mkdir(parents=True,exist_ok=True)
 rows,digest=inventory(project)
 if digest!=expected_source_inventory_sha256:raise ValueError('Project source inventory changed before axiom query')
 config=json.loads(config_file.read_text());names=config['theorem_names'];allowed=set(config['permitted_axioms'])
 if not names or len(names)!=len(set(names)) or not allowed<=STANDARD_AXIOMS:raise ValueError('Invalid selected targets or permitted axioms')
 identifier=re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
 if not identifier.fullmatch(config['solution_module']) or any(not identifier.fullmatch(name) for name in names):raise ValueError('Unsupported or unsafe Lean query identifier')
 version=subprocess.run([str(compiler),'--version'],capture_output=True,text=True,check=True).stdout.strip()
 if 'version 4.35.0,' not in version or 'commit '+COMMIT not in version:raise ValueError('Wrong native Lean compiler version or commit')
 roots=[Path(value).resolve() for value in lean_path.split(os.pathsep) if value]
 rel=Path(*config['solution_module'].split('.')).with_suffix('.olean');found=[root/rel for root in roots if (root/rel).is_file()]
 if len(found)!=1:raise ValueError('Missing or ambiguous compiled Solution module')
 output=found[0];artifacts=[output,Path(str(output)+'.private'),Path(str(output)+'.server'),output.with_suffix('.ir'),Path(str(output.with_suffix('.ir'))+'.sig')]
 if not all(p.is_file() for p in artifacts):raise ValueError('Incomplete five-artifact compiled Solution')
 artifact_records=[{'path':str(p),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in artifacts]
 query='module\n\nimport '+config['solution_module']+'\n\n'+''.join('#print axioms '+name+'\n' for name in names)
 query_file=work/'SelectedAxiomQuery.lean';query_file.write_text(query,encoding='utf-8',newline='\n');query_sha=sha(query.encode())
 command=[str(compiler),'-j1','-M12288',str(query_file)];env=dict(os.environ);env['LEAN_PATH']=lean_path;env['LEAN_NUM_THREADS']='1';env['PATH']=str(compiler.parent)+os.pathsep+env.get('PATH','')
 start=time.time();run=subprocess.run(command,cwd=work,env=env,capture_output=True,timeout=timeout);stdout=run.stdout.decode('utf-8',errors='replace');stderr=run.stderr.decode('utf-8',errors='replace');(work/'stdout.log').write_bytes(run.stdout);(work/'stderr.log').write_bytes(run.stderr)
 parsed={};duplicates=[]
 pattern=re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",re.S)
 for match in pattern.finditer(stdout):
  name=match[1];axioms=[a.strip() for a in (match[2] or '').split(',') if a.strip()]
  if name in parsed:duplicates.append(name)
  parsed[name]=axioms
 _,after_digest=inventory(project);changed_artifacts=[str(p) for p,row in zip(artifacts,artifact_records) if not p.is_file() or sha(p.read_bytes())!=row['sha256']]
 errors=[]
 if run.returncode:errors.append('Ordinary Lean query exited with code '+str(run.returncode))
 if set(parsed)!=set(names) or duplicates:errors.append('Selected theorem axiom output does not match the requested names exactly')
 extra={name:sorted(set(axioms)-allowed) for name,axioms in parsed.items() if set(axioms)-allowed}
 if extra:errors.append('Unexpected axiom dependencies: '+json.dumps(extra,sort_keys=True))
 if after_digest!=digest:errors.append('Project source inventory changed during query')
 if changed_artifacts:errors.append('Compiled Solution artifacts changed during query')
 report={'schema_version':1,'kind':'ordinary-compiled-solution-selected-axiom-query','status':'pass' if not errors else 'fail','selected_axioms_checked':not errors,'project_root':str(project),'source_inventory_sha256':digest,'source_stable':after_digest==digest,'solution_module':config['solution_module'],'theorem_names':names,'permitted_axioms':sorted(allowed),'axioms_by_theorem':parsed,'compiler_version':version,'compiler_sha256':sha(compiler.read_bytes()),'solution_artifacts':artifact_records,'query_path':str(query_file),'query_sha256':query_sha,'stdout_path':str(work/'stdout.log'),'stdout_sha256':sha(run.stdout),'stderr_path':str(work/'stderr.log'),'stderr_sha256':sha(run.stderr),'command':command,'exit_code':run.returncode,'elapsed_seconds':time.time()-start,'errors':errors,'kernel_replay_performed':False}
 (work/'selected-axioms.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');return report

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--project-root',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--lean-path',required=True);p.add_argument('--work-dir',type=Path,required=True);p.add_argument('--expected-source-inventory-sha256',required=True);p.add_argument('--config',type=Path);a=p.parse_args()
 try:result=audit_project(project_root=a.project_root,lean=a.lean,lean_path=a.lean_path,work_dir=a.work_dir,expected_source_inventory_sha256=a.expected_source_inventory_sha256,config_path=a.config)
 except (ValueError,OSError,subprocess.SubprocessError) as exc:print(json.dumps({'status':'fail','selected_axioms_checked':False,'error':str(exc),'kernel_replay_performed':False}));return 1
 print(json.dumps(result,indent=2));return 0 if result['status']=='pass' else 1
if __name__=='__main__':raise SystemExit(main())
