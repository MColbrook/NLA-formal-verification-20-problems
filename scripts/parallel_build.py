#!/usr/bin/env python3
"""Bounded, dependency-aware ordinary compilation with native Lean.

This is a development build, not Comparator, export, NanoDa or independent
kernel replay. Local modules are compiled or reused only with matching input
and output receipts; dependency oleans come from the separately pinned cache.
"""
from __future__ import annotations
import argparse,concurrent.futures,datetime,graphlib,hashlib,json,os,re,signal,subprocess,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
from lean_source import lean_code_mask

SKIP={'.git','.lake','__pycache__','.build-cache'}
def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(p):return sha(p.read_bytes())
def atomic_json(path,data):
 path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_name(path.name+'.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8');tmp.replace(path)
def inventory(project):
 rows=[]
 for directory,dirs,files in os.walk(project,followlinks=False):
  dirs[:]=sorted(d for d in dirs if d not in SKIP and not (Path(directory)==project and d=='dist') and not (Path(directory)==project/'verification' and d=='local-builds'))
  for name in sorted(files):
   p=Path(directory)/name;rel=p.relative_to(project).as_posix()
   if p.is_symlink():raise ValueError('Symlink in frozen project source: '+str(p))
   if name.endswith('.lean') or name in {'lean-toolchain','lake-manifest.json','lakefile.toml','comparator.json'}:rows.append({'path':rel,'sha256':file_sha(p)})
 rows.sort(key=lambda r:r['path']);return rows,sha(json.dumps(rows,sort_keys=True,separators=(',',':')).encode())
def imports(text):
 names=[];pending=False;identifier=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
 for raw in lean_code_mask(text).splitlines():
  line=re.sub(r'«([A-Za-z_][A-Za-z0-9_\']*)»',r'\1',raw);s=line.strip()
  if not s or s in {'module','prelude'}:continue
  m=re.match(r'(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.*)$',s)
  if m:parts=m[1].split();pending=True
  elif pending and line[:1].isspace() and all(identifier.fullmatch(x) for x in s.split()) and s.split()[0] not in {'open','namespace','section','end','variable','universe','set_option','attribute','noncomputable','public','private','def','theorem','instance'}:parts=s.split()
  else:break
  for name in parts:
   if not identifier.fullmatch(name):raise ValueError('Unsupported import name: '+name)
   if name not in names:names.append(name)
 return names

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source-root',type=Path,required=True);p.add_argument('--cache-dir',type=Path,required=True);p.add_argument('--build-dir',type=Path,required=True);p.add_argument('--report-dir',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--jobs',type=int,default=24);p.add_argument('--memory-mb',type=int,default=12288);p.add_argument('--module-timeout',type=int,default=3600);p.add_argument('--ids',nargs='*');p.add_argument('--resume',action='store_true');a=p.parse_args()
 if not 1<=a.jobs<=32:raise SystemExit('Use between 1 and 32 compiler processes')
 open_file_limit=None
 try:
  import resource
  soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE);target=1048576 if hard==resource.RLIM_INFINITY else min(hard,1048576)
  if soft<target:resource.setrlimit(resource.RLIMIT_NOFILE,(target,hard))
  open_file_limit=list(resource.getrlimit(resource.RLIMIT_NOFILE))
 except ImportError:pass
 source=a.source_root.resolve();cache=a.cache_dir.resolve();build=a.build_dir.resolve();reports=a.report_dir.resolve();lean=a.lean.resolve()
 reports.mkdir(parents=True,exist_ok=True);build.mkdir(parents=True,exist_ok=True)
 compiler={'path':str(lean),'sha256':file_sha(lean),'version':subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout.strip()}
 if 'version 4.35.0,' not in compiler['version'] or 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' not in compiler['version']:raise SystemExit('Wrong native compiler version or commit')
 index=json.loads((source/'submission-index.json').read_text());profile=json.loads((source/'dependency-profile.json').read_text())
 projects={e['id']:e for e in index.get('components', index['entries']) if not a.ids or e['id'] in a.ids}
 if a.ids and set(a.ids)!=set(projects):raise SystemExit('Unknown selected project')
 packages=cache/'.lake/packages';external_roots=[(row['name'],packages/row['name']) for row in profile['packages']]
 for name,root in external_roots:
  if not root.is_dir():raise SystemExit('Missing pinned dependency: '+name)
 external_cache={};external_used={};nodes={};graph={};project_inputs={};environments={}
 def external(module):
  if module in external_cache:return external_cache[module]
  rel=Path(*module.split('.')).with_suffix('.olean');found=[]
  for name,root in external_roots:
   output=root/'.lake/build/lib/lean'/rel
   if output.is_file():found.append((name,output))
  if not found:
   core=lean.parent.parent/'lib/lean'/rel
   if core.is_file():found=[('Lean-core',core)]
  if len(found)!=1:raise ValueError('Missing or ambiguous dependency olean: '+module+' '+repr(found))
  name,output=found[0];value={'package':name,'path':str(output),'sha256':file_sha(output)}
  external_cache[module]=value;external_used[module]=value;return value
 def visit(pid,module,active):
  key=pid+'::'+module
  if key in nodes:return key
  if key in active:raise ValueError('Import cycle at '+key)
  project=source/projects[pid]['project_path'];rel=Path(*module.split('.'));src=project/rel.with_suffix('.lean')
  if not src.is_file():raise ValueError('Missing local source '+key)
  active.add(key);data=src.read_bytes();deps=[];outside={}
  for dependency in imports(data.decode('utf-8-sig')):
   if (project/Path(*dependency.split('.')).with_suffix('.lean')).is_file():deps.append(visit(pid,dependency,active))
   else:outside[dependency]=external(dependency)
  active.remove(key)
  nodes[key]={'id':pid,'module':module,'source':src,'source_sha256':sha(data),'dependencies':deps,'external_imports':outside};graph[key]=set(deps);return key
 targets={}
 for pid,entry in projects.items():
  project=source/entry['project_path'];rows,digest=inventory(project);project_inputs[pid]={'files':rows,'sha256':digest,'toolchain':(project/'lean-toolchain').read_text().strip()}
  if project_inputs[pid]['toolchain']!=profile['toolchain']:raise ValueError('Project/toolchain mismatch: '+pid)
  config=json.loads((source/entry['comparator_config_path']).read_text());targets[pid]=[visit(pid,config[name],set()) for name in ('challenge_module','solution_module')]
  # Keep auxiliary development environments separate, while compiling every staged source.
  for row in rows:
   if row['path'].endswith('.lean') and row['path']!='lakefile.lean':visit(pid,row['path'][:-5].replace('/','.'),set())
  env=dict(os.environ);env['LEAN_NUM_THREADS']='1';env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join([str(build/pid/'lib/lean')]+[str(root/'.lake/build/lib/lean') for _,root in external_roots]);env['TMPDIR']=str(build/pid/'tmp');Path(env['TMPDIR']).mkdir(parents=True,exist_ok=True);environments[pid]=env
 atomic_json(reports/'build-plan.json',{'kind':'ordinary-native-lean-build','all_local_modules':True,'compiler':compiler,'jobs':a.jobs,'open_file_limit':open_file_limit,'lean_num_threads':1,'memory_mb_per_process':a.memory_mb,'node_count':len(nodes),'projects':{pid:{'source_inventory_sha256':v['sha256'],'toolchain':v['toolchain'],'targets':targets[pid]} for pid,v in project_inputs.items()},'external_oleans':external_used,'profile_sha256':file_sha(source/'dependency-profile.json'),'kernel_replay_performed':False})
 state={};cancel=False;processes={}
 def stop(signum,frame):
  nonlocal cancel;cancel=True
  for child in list(processes.values()):
   try:child.terminate()
   except ProcessLookupError:pass
 signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
 def compile_one(key):
  node=nodes[key];pid=node['id'];module=node['module'];project=source/projects[pid]['project_path'];relative=Path(*module.split('.'));output=build/pid/'lib/lean'/relative.with_suffix('.olean');stamp=output.with_suffix('.standard-build.json');log=reports/'module-logs'/pid/relative.with_suffix('.log');output.parent.mkdir(parents=True,exist_ok=True);log.parent.mkdir(parents=True,exist_ok=True)
  expected_artifacts=[output,Path(str(output)+'.private'),Path(str(output)+'.server'),output.with_suffix('.ir'),Path(str(output.with_suffix('.ir'))+'.sig')]
  binding={'source_sha256':node['source_sha256'],'compiler_sha256':compiler['sha256'],'module':module,'imports':{dep:state[dep]['signature'] for dep in node['dependencies']},'external_imports':node['external_imports']};signature=sha(json.dumps(binding,sort_keys=True,separators=(',',':')).encode())
  if a.resume and stamp.is_file():
   prior=json.loads(stamp.read_text())
   if prior.get('signature')==signature and prior.get('status')=='pass' and {x['path'] for x in prior.get('artifacts',[])}=={str(p) for p in expected_artifacts} and all(Path(x['path']).is_file() and file_sha(Path(x['path']))==x['sha256'] for x in prior.get('artifacts',[])) and prior.get('artifacts'):
    return {**prior,'reused':True}
  command=[str(lean),'-j1','-M'+str(a.memory_mb),'-o',str(output),str(node['source'])];started=time.time()
  print(json.dumps({'event':'BUILD','project':pid,'module':module}),flush=True)
  result={'kind':'ordinary-native-lean-module','id':pid,'module':module,'command':command,'source_sha256':node['source_sha256'],'signature':signature,'binding':binding,'started_at':started,'reused':False,'log':str(log),'kernel_replay_performed':False}
  with log.open('wb') as stream:
   try:
    child=subprocess.Popen(command,cwd=project,env=environments[pid],stdout=stream,stderr=subprocess.STDOUT);processes[key]=child
    try:code=child.wait(timeout=a.module_timeout or None)
    except subprocess.TimeoutExpired:child.kill();code=child.wait();result['timeout']=True
    finally:processes.pop(key,None)
    result['exit_code']=code
   except BaseException as exc:result.update(exit_code=-1,error=str(exc))
  stable=file_sha(node['source'])==node['source_sha256'];artifacts=[{'path':str(f),'sha256':file_sha(f),'bytes':f.stat().st_size} for f in expected_artifacts if f.is_file()]
  result.update(status='pass' if result['exit_code']==0 and stable and all(p.is_file() for p in expected_artifacts) else 'fail',source_stable=stable,finished_at=time.time(),elapsed_seconds=time.time()-started,artifacts=artifacts,log_sha256=file_sha(log))
  if result['status']=='pass':atomic_json(stamp,result)
  atomic_json(log.with_suffix('.json'),result);print(json.dumps({'event':result['status'].upper(),'project':pid,'module':module,'seconds':round(result['elapsed_seconds'],3)}),flush=True);return result
 started=time.time();sorter=graphlib.TopologicalSorter(graph);sorter.prepare();running={};all_records=[]
 def report_progress(final=False):
  rows=[]
  for pid,input in project_inputs.items():
   selected=[r for key,r in state.items() if key.startswith(pid+'::')];project_nodes=[key for key in nodes if key.startswith(pid+'::')];after,after_digest=inventory(source/projects[pid]['project_path']);stable=after_digest==input['sha256'];passed=all(key in state and state[key]['status']=='pass' for key in project_nodes) and stable
   rows.append({'id':pid,'all_project_modules_compiled':passed,'status':'pass' if passed else ('fail' if any(r['status'] in {'fail','blocked'} for r in selected) else 'in-progress'),'toolchain':input['toolchain'],'source_inventory_sha256':input['sha256'],'source_stable':stable,'target_modules':[nodes[key]['module'] for key in targets[pid]],'modules_total':len(project_nodes),'modules_passed':sum(r['status']=='pass' for r in selected),'modules_failed':sum(r['status']=='fail' for r in selected),'modules_blocked':sum(r['status']=='blocked' for r in selected),'kind':'ordinary-native-source-compilation','compiler_version':compiler['version'],'compiler_sha256':compiler['sha256'],'kernel_replay_performed':False})
  value={'schema_version':1,'all_project_modules_compiled':all(r['all_project_modules_compiled'] for r in rows),'status':'pass' if all(r['status']=='pass' for r in rows) else ('fail' if final else 'in-progress'),'kind':'ordinary-native-source-compilation','compiler':compiler,'jobs':a.jobs,'lean_num_threads':1,'elapsed_seconds':time.time()-started,'kernel_replay_performed':False,'projects':rows,'modules_completed':len(state),'modules_total':len(nodes),'cancelled':cancel}
  atomic_json(reports/'build-status.json',value);return value
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as executor:
  ready=[];last_report=0
  while sorter.is_active() or running:
   ready.extend(sorter.get_ready());ready.sort(key=lambda key:(0 if nodes[key]['module']=='Challenge' else 1,0 if nodes[key]['id'] in {'MD-06','MI-22'} else 1,key))
   while ready and len(running)<a.jobs and not cancel:
    key=ready.pop(0);bad=[dep for dep in graph[key] if state[dep]['status']!='pass']
    if bad:
     result={'status':'blocked','id':nodes[key]['id'],'module':nodes[key]['module'],'failed_dependencies':bad};state[key]=result;sorter.done(key);continue
    running[executor.submit(compile_one,key)]=key
   if cancel:
    for key in ready:state[key]={'status':'blocked','id':nodes[key]['id'],'module':nodes[key]['module'],'reason':'cancelled'};sorter.done(key)
    ready=[]
   if running:
    completed,_=concurrent.futures.wait(running,timeout=3,return_when=concurrent.futures.FIRST_COMPLETED)
    for future in completed:
     key=running.pop(future)
     try:state[key]=future.result()
     except BaseException as exc:state[key]={'status':'fail','id':nodes[key]['id'],'module':nodes[key]['module'],'error':str(exc)}
     sorter.done(key)
   if time.time()-last_report>15:report_progress();last_report=time.time()
  report=report_progress(True)
 atomic_json(reports/'module-results.json',{'compiler':compiler,'records':[state[k] for k in sorted(state)],'kernel_replay_performed':False})
 print(json.dumps(report),flush=True);return 0 if report['status']=='pass' else 1
if __name__=='__main__':raise SystemExit(main())
