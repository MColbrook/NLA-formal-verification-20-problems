#!/usr/bin/env python3
"""Materialize exact public Git pins and fetch Mathlib's ordinary build cache.

No source is submitted to a service. No Comparator or independent-kernel replay
is run. Git dependencies are fetched directly at committed revisions; this
helper never runs lake update or dependency post-update hooks.
"""
from __future__ import annotations
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def sha_file(file):return hashlib.sha256(file.read_bytes()).hexdigest()
def run(command,cwd,env):
 print(json.dumps({'event':'dependency-command','command':command,'cwd':str(cwd)}),flush=True)
 subprocess.run(command,cwd=cwd,env=env,check=True)
def prepare(profile_file,cache,lake,git_jobs=3,fetch_cache=True,force_cache=False):
 open_file_limit=None
 try:
  import resource
  soft,hard=resource.getrlimit(resource.RLIMIT_NOFILE);target=1048576 if hard==resource.RLIM_INFINITY else min(hard,1048576)
  if soft<target:resource.setrlimit(resource.RLIMIT_NOFILE,(target,hard))
  open_file_limit=list(resource.getrlimit(resource.RLIMIT_NOFILE))
 except ImportError:pass
 profile=json.loads(profile_file.read_text(encoding='utf-8'))
 if profile.get('toolchain')!='leanprover/lean4:v4.35.0':raise ValueError('Unexpected dependency toolchain')
 if profile.get('mathlib_revision')!='56a005855ea17e0b0958f73ec801ae140b0a1679':raise ValueError('Unexpected canonical Mathlib pin')
 if any(p['name'].lower()=='leancert' for p in profile['packages']):raise ValueError('This source build profile must be Mathlib-only')
 cache=cache.resolve();cache.mkdir(parents=True,exist_ok=True)
 packages=cache/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
 env=dict(os.environ);env.update(GIT_CONFIG_GLOBAL=os.devnull,GIT_CONFIG_NOSYSTEM='1',GIT_TERMINAL_PROMPT='0',GIT_LFS_SKIP_SMUDGE='1',GIT_NO_REPLACE_OBJECTS='1',LEAN_NUM_THREADS='1',RAYON_NUM_THREADS='24',MATHLIB_NO_CACHE='1')
 env['PATH']=str(lake.resolve().parent)+os.pathsep+env.get('PATH','')
 env['TMPDIR']=str(cache/'tmp');env['TMP']=env['TMPDIR'];env['TEMP']=env['TMPDIR'];Path(env['TMPDIR']).mkdir(exist_ok=True)
 env['XDG_CACHE_HOME']=str(cache/'download-cache');env['MATHLIB_CACHE_DIR']=str(cache/'download-cache/mathlib')
 def materialize(package):
  name=package['name'];url=package['url'];revision=package['rev']
  if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',name):raise ValueError('Unsafe package name')
  if not re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?',url):raise ValueError('Dependency is not public credential-free GitHub')
  if not re.fullmatch(r'[0-9a-f]{40}',revision):raise ValueError('Dependency is not pinned')
  destination=packages/name
  if not destination.exists():
   destination.mkdir()
   run(['git','-c','core.hooksPath=/dev/null','init','-q'],destination,env)
   run(['git','remote','add','origin',url],destination,env)
   run(['git','-c','core.hooksPath=/dev/null','-c','protocol.file.allow=never','fetch','--depth=1','--no-tags','origin',revision],destination,env)
   run(['git','-c','core.hooksPath=/dev/null','checkout','-q','--detach','FETCH_HEAD'],destination,env)
  head=subprocess.run(['git','rev-parse','HEAD'],cwd=destination,env=env,check=True,capture_output=True,text=True).stdout.strip()
  if head!=revision:raise ValueError('Existing dependency does not match pin: '+name)
  diff=subprocess.run(['git','--no-optional-locks','diff','--no-ext-diff','--no-textconv','--exit-code','HEAD','--'],cwd=destination,env=env,capture_output=True,text=True)
  if diff.returncode:raise ValueError('Dependency has modified tracked source: '+name)
  return {'name':name,'url':url,'revision':head,'tracked_source_clean':True}
 with concurrent.futures.ThreadPoolExecutor(max_workers=git_jobs) as executor:resolved=list(executor.map(materialize,profile['packages']))
 (cache/'lean-toolchain').write_text(profile['toolchain']+'\n',encoding='utf-8')
 (cache/'lakefile.toml').write_text('name = "nla_dependency_cache"\nversion = "1.0.0"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "'+profile['mathlib_revision']+'"\n',encoding='utf-8')
 manifest=dict(version='1.3.0',packagesDir='.lake/packages',packages=profile['packages'],name='nla_dependency_cache',lakeDir='.lake',fixedToolchain=False)
 (cache/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
 expected=(packages/'mathlib/lean-toolchain').read_text().strip()
 if expected!=profile['toolchain']:raise ValueError('Canonical Mathlib toolchain mismatch')
 started=time.time()
 if fetch_cache:run([str(lake.resolve()),'--keep-toolchain','exe','cache','get!' if force_cache else 'get'],cache,env)
 actual=json.loads((cache/'lake-manifest.json').read_text())
 if {(p['name'],p['rev']) for p in actual['packages']}!={(p['name'],p['rev']) for p in profile['packages']}:raise ValueError('Dependency revisions changed')
 report={'status':'pass','kind':'ordinary-pinned-dependency-cache','cache_dir':str(cache),'packages_dir':str(packages),'profile_sha256':sha_file(profile_file),'toolchain':profile['toolchain'],'resolved_packages':resolved,'cache_fetch_performed':fetch_cache,'force_cache':force_cache,'open_file_limit':open_file_limit,'cache_elapsed_seconds':time.time()-started,'kernel_replay_performed':False}
 (cache/'dependency-status.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(report),flush=True);return report

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--lake',type=Path,default=shutil.which('lake'));p.add_argument('--cache-dir',type=Path,default=Path(tempfile.gettempdir())/'nla-palomar-deps-4.35.0');p.add_argument('--profile',type=Path,default=ROOT/'dependency-profile.json');p.add_argument('--git-jobs',type=int,default=3);p.add_argument('--prepare-only',action='store_true');p.add_argument('--force-cache',action='store_true');a=p.parse_args()
 if not a.lake:raise SystemExit('Specify the pinned native Lake executable')
 prepare(a.profile,a.cache_dir,Path(a.lake),a.git_jobs,not a.prepare_only,a.force_cache)
if __name__=='__main__':main()
