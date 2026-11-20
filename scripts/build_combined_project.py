"""Stage and compile the single root Palomar project, preserving component sources."""
from __future__ import annotations
import argparse,concurrent.futures,graphlib,hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'scripts'))
from parallel_build import inventory,imports
from audit_selected_axioms import audit_project
def sha(data):return hashlib.sha256(data).hexdigest()
def atomic_json(path,value):
 path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_name(path.name+'.tmp')
 tmp.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8');tmp.replace(path)
def stage_sources(check=False):
 index=json.loads((ROOT/'submission-index.json').read_text());components=index.get('components',index['entries']);expected={}
 for component in components:
  project=ROOT/component['project_path'];sources=list((project/'NLA').rglob('*.lean'))
  sources.extend(f for f in project.glob('*.lean') if f.name not in {'Challenge.lean','Solution.lean'})
  for src in sources:
   dest=('NLA/Collection/'+component['id'].replace('-','')+'PaperSolution.lean') if src.parent==project and src.name=='PaperSolution.lean' else src.relative_to(project).as_posix()
   data=src.read_bytes()
   if dest in expected and expected[dest]['data']!=data:raise ValueError('Conflicting proof modules: '+dest)
   expected.setdefault(dest,{'data':data,'sources':[]})['sources'].append(src.relative_to(ROOT).as_posix())
 map_path=ROOT/'audit/combined-source-map.json';previous=json.loads(map_path.read_text()) if map_path.exists() else {'files':[]}
 old_hashes={row['path']:row['sha256'] for row in previous['files']}
 for old in previous['files']:
  if old['path'] not in expected:
   stale=ROOT/old['path']
   if not stale.resolve().is_relative_to((ROOT/'NLA').resolve()):raise ValueError('Unsafe stale generated path')
   if stale.exists():
    if check:raise ValueError('Unexpected stale unified module: '+old['path'])
    if sha(stale.read_bytes())!=old['sha256']:raise ValueError('Modified generated module: '+old['path'])
    stale.unlink()
 rows=[]
 for dest,row in sorted(expected.items()):
  path=ROOT/dest
  if check:
   if not path.is_file() or path.read_bytes()!=row['data']:raise ValueError('Unified copy differs: '+dest)
  elif not path.exists() or path.read_bytes()!=row['data']:
   if path.exists() and sha(path.read_bytes())!=old_hashes.get(dest):raise ValueError('Refusing to overwrite modified generated module: '+dest)
   path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(row['data'])
  rows.append({'path':dest,'sha256':sha(row['data']),'source_paths':sorted(row['sources']),'transformation':'byte-identical copy; unique module path' if dest.startswith('NLA/Collection/') else 'byte-identical deduplicated copy'})
 value={'schema_version':1,'kind':'unified-proof-source-map','original_components_preserved':True,'component_count':len(components),'unique_modules':len(rows),'files':rows}
 if check:
  if not map_path.is_file() or json.loads(map_path.read_text())!=value:raise ValueError('Unified source map is stale')
 else:atomic_json(map_path,value)
 return value
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--stage-only',action='store_true');p.add_argument('--check',action='store_true')
 p.add_argument('--lean',type=Path);p.add_argument('--cache-dir',type=Path,default=Path(tempfile.gettempdir())/'nla-palomar-deps-4.35.0')
 p.add_argument('--jobs',type=int,default=1);p.add_argument('--memory-mb',type=int,default=4096);p.add_argument('--module-timeout',type=int,default=3600)
 a=p.parse_args();staged=stage_sources(a.check);print(json.dumps({'stage':'unified-source','status':'pass','unique_modules':staged['unique_modules']}),flush=True)
 if a.check or a.stage_only:return 0
 if a.lean is None:p.error('--lean is required for compilation')
 if not 1<=a.jobs<=16:p.error('--jobs must be between 1 and 16')
 lean=a.lean.resolve();version=subprocess.check_output([str(lean),'--version'],text=True).strip()
 if 'version 4.35.0,' not in version or 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' not in version:raise ValueError('Wrong native Lean: '+version)
 compiler_sha=sha(lean.read_bytes());_,digest=inventory(ROOT);config=json.loads((ROOT/'comparator.json').read_text());profile=json.loads((ROOT/'dependency-profile.json').read_text())
 packages=a.cache_dir.resolve()/'.lake/packages';deps=[packages/row['name'] for row in profile['packages']]
 if not all(path.is_dir() for path in deps):raise ValueError('Missing pinned dependency cache')
 output_root=ROOT/'.lake/build/lib/lean';logs=ROOT/'verification/local-builds/combined';logs.mkdir(parents=True,exist_ok=True)
 env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(output_root)]+[str(path/'.lake/build/lib/lean') for path in deps]);env['LEAN_NUM_THREADS']='1';env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 nodes={};graph={};external_cache={}
 def external(module):
  if module not in external_cache:
   rel=Path(*module.split('.')).with_suffix('.olean');found=[path for path in [d/'.lake/build/lib/lean'/rel for d in deps]+[lean.parent.parent/'lib/lean'/rel] if path.is_file()]
   if len(found)!=1:raise ValueError('Missing or ambiguous pinned import: '+module)
   external_cache[module]={'path':str(found[0]),'sha256':sha(found[0].read_bytes())}
  return external_cache[module]
 def visit(module,active):
  if module in nodes:return
  if module in active:raise ValueError('Import cycle: '+module)
  active.add(module);src=ROOT/Path(*module.split('.')).with_suffix('.lean');data=src.read_bytes();local=[];outside={}
  for dependency in imports(data.decode('utf-8-sig')):
   path=ROOT/Path(*dependency.split('.')).with_suffix('.lean')
   if path.is_file():visit(dependency,active);local.append(dependency)
   else:outside[dependency]=external(dependency)
  active.remove(module);nodes[module]={'source':src,'sha256':sha(data),'imports':local,'external':outside};graph[module]=set(local)
 for target in (config['challenge_module'],config['solution_module']):visit(target,set())
 print(json.dumps({'stage':'build-plan','modules':len(nodes),'jobs':a.jobs}),flush=True);state={}
 def compile_one(module):
  node=nodes[module];rel=Path(*module.split('.'));out=output_root/rel.with_suffix('.olean');stamp=out.with_suffix('.combined-source.json')
  artifacts=[out,Path(str(out)+'.private'),Path(str(out)+'.server'),out.with_suffix('.ir'),Path(str(out.with_suffix('.ir'))+'.sig')]
  binding={'source_sha256':node['sha256'],'compiler_sha256':compiler_sha,'module':module,'imports':{name:state[name]['signature'] for name in node['imports']},'external':node['external']}
  signature=sha(json.dumps(binding,sort_keys=True,separators=(',',':')).encode())
  if stamp.is_file():
   prior=json.loads(stamp.read_text())
   if prior.get('signature')==signature and prior.get('status')=='pass' and {row.get('path') for row in prior.get('artifacts',[])}=={str(path) for path in artifacts} and len(prior.get('artifacts',[]))==len(artifacts) and all(Path(row['path']).is_file() and sha(Path(row['path']).read_bytes())==row['sha256'] for row in prior['artifacts']):return {**prior,'reused':True}
  out.parent.mkdir(parents=True,exist_ok=True);log=logs/rel.with_suffix('.log');log.parent.mkdir(parents=True,exist_ok=True)
  command=[str(lean),'-j1','-M'+str(a.memory_mb),'-o',str(out),str(node['source'])];start=time.time();print(json.dumps({'event':'BUILD','module':module}),flush=True)
  with log.open('wb') as stream:run=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=a.module_timeout)
  stable=sha(node['source'].read_bytes())==node['sha256'];passed=run.returncode==0 and stable and all(path.is_file() for path in artifacts)
  row={'module':module,'status':'pass' if passed else 'fail','signature':signature,'source_stable':stable,'source_sha256':node['sha256'],'exit_code':run.returncode,'seconds':time.time()-start,'log':log.relative_to(ROOT).as_posix(),'reused':False,'artifacts':[{'path':str(path),'sha256':sha(path.read_bytes())} for path in artifacts if path.is_file()]}
  if passed:atomic_json(stamp,row)
  print(json.dumps({'event':row['status'].upper(),'module':module,'seconds':round(row['seconds'],3)}),flush=True);return row
 start=time.time();sorter=graphlib.TopologicalSorter(graph);sorter.prepare();pending={};ready=[];abort_challenge=False
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as executor:
  while sorter.is_active() or pending:
   ready.extend(sorter.get_ready());ready.sort(key=lambda m:(m!=config['challenge_module'],m))
   while ready and len(pending)<a.jobs:
    module=ready.pop(0)
    if abort_challenge or any(state[d]['status']!='pass' for d in graph[module]):state[module]={'module':module,'status':'blocked','signature':'','exit_code':-1};sorter.done(module)
    else:pending[executor.submit(compile_one,module)]=module
   if pending:
    finished,_=concurrent.futures.wait(pending,timeout=3,return_when=concurrent.futures.FIRST_COMPLETED)
    for future in finished:
     module=pending.pop(future)
     try:state[module]=future.result()
     except BaseException as error:state[module]={'module':module,'status':'fail','signature':'','exit_code':-1,'error':repr(error)}
     if module==config['challenge_module'] and state[module]['status']!='pass':abort_challenge=True
     sorter.done(module)
 _,after=inventory(ROOT);stable=after==digest;passed=stable and all(r['status']=='pass' for r in state.values());axiom=None;error=None;public=ROOT/'verification/selected-axioms/NLA20'
 if passed:
  try:
   work=Path(tempfile.gettempdir())/'nla-palomar-combined-selected-axioms-4.35.0';axiom=audit_project(project_root=ROOT,lean=lean,lean_path=env['LEAN_PATH'],work_dir=work,expected_source_inventory_sha256=digest);public.mkdir(parents=True,exist_ok=True)
   for original,name in [('SelectedAxiomQuery.lean','query.txt'),('stdout.log','stdout.txt'),('stderr.log','stderr.txt')]:shutil.copyfile(work/original,public/name)
   axiom['project_root']='.'
   for role,name in [('query','query.txt'),('stdout','stdout.txt'),('stderr','stderr.txt')]:axiom[role+'_path']=(public/name).relative_to(ROOT).as_posix()
   atomic_json(public/'selected-axioms.json',axiom)
  except Exception as exc:error=repr(exc)
 selected=bool(axiom and axiom.get('selected_axioms_checked') and not error)
 row={'id':'NLA20','status':'pass' if passed and selected else 'fail','combined_solution_compiled':passed,'combined_challenge_compiled':passed,'source_inventory_sha256':digest,'toolchain':(ROOT/'lean-toolchain').read_text().strip(),'compiler_version':version,'compiler_sha256':compiler_sha,'source_stable':stable,'exit_code':0 if passed and selected else 1,'selected_axioms_checked':selected,'selected_axioms_receipt':'verification/selected-axioms/NLA20/selected-axioms.json' if axiom else None,'selected_axioms_receipt_sha256':sha((public/'selected-axioms.json').read_bytes()) if axiom else None,'selected_axioms_query_sha256':axiom.get('query_sha256') if axiom else None,'selected_axioms_stdout_sha256':axiom.get('stdout_sha256') if axiom else None,'selected_axiom_error':error,'challenge_artifacts':state[config['challenge_module']].get('artifacts',[]),'solution_artifacts':state[config['solution_module']].get('artifacts',[]),'modules_in_combined_closure':len(nodes),'modules_failed':[m for m,r in state.items() if r['status']=='fail'],'elapsed_seconds':time.time()-start,'kernel_replay_performed':False}
 report={'schema_version':1,'kind':'ordinary-combined-source-compilation','status':row['status'],'projects':[row],'kernel_replay_performed':False}
 atomic_json(ROOT/'verification/combined-build-status.json',report);atomic_json(logs/'module-results.json',{'modules':[state[m] for m in sorted(state)],'source_inventory_sha256':digest});print(json.dumps(report),flush=True)
 return 0 if row['status']=='pass' else 1
if __name__=='__main__':raise SystemExit(main())
