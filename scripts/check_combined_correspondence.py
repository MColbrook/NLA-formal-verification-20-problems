"""Run the bundled Comparator core on independently compiled environments.
This local diagnostic does not perform full proof export or kernel replay,
invoke external kernels, or claim official Palomar verification.
"""
from __future__ import annotations
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from parallel_build import inventory
def sha(data):return hashlib.sha256(data).hexdigest()
PRIMITIVE=['Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam']
TEMPLATE=r'''
module
public import Lean
public import Lake.Check.Compare
public import Lake.Check.Util
public import Lean.CompactedRegion
@[expose] public section
open Lean
def theoremNames : Array Name := __THEOREMS__
def permittedAxioms : Array Name := __AXIOMS__
def primitiveNames : Array Name := __PRIMITIVE__
def referenced (info : ConstantInfo) : Array Name :=
  let action : StateM (Array Name) Unit :=
    Lake.Check.runForUsedConsts info fun name => modify fun names => names.push name
  (action.run #[]).2
partial def collect (env : Environment) (targets seeds : Array Name) : Except String LeanExport.ExportedEnv := do
  let targetSet := Std.HashSet.ofArray targets
  let mut work := seeds
  let mut result : LeanExport.ExportedEnv := {constMap := {},constOrder := #[]}
  while !work.isEmpty do
    let name := work.back!
    work := work.pop
    if result.constMap.contains name then continue
    let some info := env.find? name | throw s!"Missing compiled constant: {name}"
    let stored := if targetSet.contains name then
        match info with
        | .thmInfo value => .thmInfo {value with value := mkConst __TICK____TICK__False}
        | other => other
      else info
    result := {constMap := result.constMap.insert name stored,constOrder := result.constOrder.push name}
    if targetSet.contains name then work := work ++ info.type.getUsedConstants
    else work := work ++ referenced info
  return result

/- Expression normalization follows LeanExport.Basic.removeMData.
Copyright (c) 2025 Lean FRO, LLC. Apache-2.0. -/
def normalizeExportExprM (e : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
  if let some cached := (← get)[e]? then return cached
  let normalized ← match e with
    | .mdata _ inner => normalizeExportExprM inner
    | .fvar .. | .mvar .. => unreachable!
    | .bvar .. | .sort .. | .const .. | .lit _ => pure e
    | .app f a => pure <| e.updateApp! (← normalizeExportExprM f) (← normalizeExportExprM a)
    | .lam _ d b _ => pure <| e.updateLambdaE! (← normalizeExportExprM d) (← normalizeExportExprM b)
    | .letE _ d v b _ => pure <| e.updateLet! (← normalizeExportExprM d) (← normalizeExportExprM v) (← normalizeExportExprM b) false
    | .forallE _ d b _ => pure <| e.updateForallE! (← normalizeExportExprM d) (← normalizeExportExprM b)
    | .proj _ _ value => pure <| e.updateProj! (← normalizeExportExprM value)
  modify fun cache => cache.insert e normalized
  return normalized
def normalizeExportExpr (e : Expr) : Expr := (normalizeExportExprM e).run' {}
def normalizeExportInfo (info : ConstantInfo) : ConstantInfo :=
  match info with
  | .axiomInfo value => .axiomInfo {value with type := normalizeExportExpr value.type}
  | .defnInfo value => .defnInfo {value with type := normalizeExportExpr value.type, value := normalizeExportExpr value.value}
  | .thmInfo value => .thmInfo {value with type := normalizeExportExpr value.type, value := normalizeExportExpr value.value}
  | .opaqueInfo value => .opaqueInfo {value with type := normalizeExportExpr value.type, value := normalizeExportExpr value.value}
  | .quotInfo value => .quotInfo {value with type := normalizeExportExpr value.type}
  | .inductInfo value => .inductInfo {value with type := normalizeExportExpr value.type}
  | .ctorInfo value => .ctorInfo {value with type := normalizeExportExpr value.type}
  | .recInfo value => .recInfo {value with type := normalizeExportExpr value.type, rules := value.rules.map fun rule => {rule with rhs := normalizeExportExpr rule.rhs}}
def normalizeSnapshot (input : LeanExport.ExportedEnv) : LeanExport.ExportedEnv := Id.run do
  let mut result := input
  for (name, info) in input.constMap.toList do
    result := {result with constMap := result.constMap.insert name (normalizeExportInfo info)}
  return result

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let targets := theoremNames ++ permittedAxioms
  match args with
  | ["materialize", moduleName, output] => do
    let env ← importModules #[{module := moduleName.toName}] {} (loadExts := false)
    let closure ← IO.ofExcept <| collect env targets (targets ++ primitiveNames)
    let _ ← CompactedRegion.save (α := LeanExport.ExportedEnv) output
      (Name.mkSimple ("PalomarComparatorClosure" ++ moduleName)) closure #[] none
    IO.println <| "MATERIALIZED " ++ moduleName ++ " " ++ toString closure.constMap.size
    return 0
  | ["compare", challengeFile, solutionFile] => do
    let (challenge, challengeRegion) ← CompactedRegion.read (α := LeanExport.ExportedEnv) challengeFile #[]
    let (solution, solutionRegion) ← CompactedRegion.read (α := LeanExport.ExportedEnv) solutionFile #[]
    -- Keep strong owners in an IO reference through all comparisons. The maps
    -- retain region pointers; no region is freed while those references are live.
    let regionOwners ← IO.mkRef (challengeRegion, solutionRegion)
    let challenge := normalizeSnapshot challenge
    let solution := normalizeSnapshot solution
    for name in theoremNames do
      match challenge.constMap[name]?, solution.constMap[name]? with
      | some (.thmInfo _), some (.thmInfo _) => pure ()
      | _, _ => throw <| IO.userError s!"Configured target is not a theorem on both sides: {name}"
    IO.ofExcept <| Lake.Check.compareAt challenge solution targets #[] primitiveNames
    let first := theoremNames[0]!
    let some (.thmInfo value) := solution.constMap[first]? | throw <| IO.userError "Missing type control"
    let badType := {solution with constMap := solution.constMap.insert first (.thmInfo {value with type := mkConst __TICK____TICK__False})}
    match Lake.Check.compareAt challenge badType targets #[] primitiveNames with
    | .error _ => pure ()
    | .ok _ => throw <| IO.userError "Comparator accepted a changed target type"
    let fixed := __TICK__NLA.MF05.Paper.realSpectralNorm
    let some (.defnInfo value) := solution.constMap[fixed]? | throw <| IO.userError "Missing definition control"
    let badValue := {solution with constMap := solution.constMap.insert fixed (.defnInfo {value with value := mkConst __TICK____TICK__False})}
    match Lake.Check.compareAt challenge badValue targets #[] primitiveNames with
    | .error _ => pure ()
    | .ok _ => throw <| IO.userError "Comparator accepted a changed ordinary definition"
    let ownedRegions ← regionOwners.get
    IO.println <| "CORRESPONDENCE " ++ (Json.mkObj [
      ("challenge_materialized_bytes",toJson ownedRegions.1.size.toNat),
      ("solution_materialized_bytes",toJson ownedRegions.2.size.toNat),
      ("status","pass"),("compared_theorems",toJson theoremNames.size),("selected_declarations_are_theorems",toJson true),
      ("challenge_closure_constants",toJson challenge.constMap.size),
      ("solution_closure_constants",toJson solution.constMap.size),
      ("type_negative_control",toJson true),("definition_body_negative_control",toJson true)]).compress
    return 0
  | _ => throw <| IO.userError "Expected materialize MODULE FILE or compare CHALLENGE SOLUTION"

'''

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--lean',type=Path,required=True)
 parser.add_argument('--cache-dir',type=Path,default=Path(tempfile.gettempdir())/'nla-palomar-deps-4.35.0')
 parser.add_argument('--work-dir',type=Path,default=Path(tempfile.gettempdir())/'nla-palomar-combined-correspondence-4.35.0')
 parser.add_argument('--compile-only',action='store_true')
 parser.add_argument('--timeout',type=int,default=3600)
 parser.add_argument('--memory-mb',type=int,default=8192)
 args=parser.parse_args()
 config_bytes=(ROOT/'comparator.json').read_bytes()
 config=json.loads(config_bytes)
 if config.get('definition_names',[])!=[]:raise ValueError('Expected no definition holes')
 if any(name.startswith('_private.') for name in config['theorem_names']):raise ValueError('Comparison targets must be stable public names')
 if config.get('challenge_module')!='Challenge' or config.get('solution_module')!='Solution':raise ValueError('Expected root Challenge/Solution modules')
 lean=args.lean.resolve()
 prefix=lean.parent.parent
 suffix='.exe' if os.name=='nt' else ''
 leanc=lean.parent/('leanc'+suffix)
 clang=lean.parent/('clang'+suffix)
 lake_library=prefix/'lib/lean/libLake.a'
 export_library=prefix/'lib/lean/libLeanExport.a'
 native_paths={'leanc':leanc,'clang':clang,'lake_static_library':lake_library,'export_static_library':export_library}
 clang_shared=lean.parent/'libclang-cpp.dll'
 if clang_shared.is_file():native_paths['clang_shared_library']=clang_shared
 for role,path in native_paths.items():
  if not path.is_file():raise ValueError('Pinned native toolchain input is missing: '+role+' '+str(path))
 native_inputs={role:{'path':str(path),'sha256':sha(path.read_bytes())} for role,path in native_paths.items()}
 version=subprocess.check_output([str(lean),'--version'],text=True).strip()
 if 'version 4.35.0,' not in version or 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' not in version:raise ValueError('Wrong compiler: '+version)
 compiler_digest=sha(lean.read_bytes())
 driver_digest=sha(Path(__file__).read_bytes())
 def literal(names):return '#['+', '.join(chr(96)+name for name in names)+']'
 query=TEMPLATE.replace('__THEOREMS__',literal(config['theorem_names'])).replace('__AXIOMS__',literal(config['permitted_axioms'])).replace('__PRIMITIVE__',literal(PRIMITIVE)).replace('__TICK__',chr(96))
 work=args.work_dir.resolve()
 if work==ROOT or work.is_relative_to(ROOT):raise ValueError('Comparison work directory must be outside source inputs')
 work.mkdir(parents=True,exist_ok=True)
 source=work/'CombinedCorrespondence.lean'
 source.write_text(query,encoding='utf-8',newline='\n')
 query_digest=sha(query.encode())
 cfile=work/'CombinedCorrespondence.c'
 executable=work/('CombinedCorrespondence'+suffix)
 profile=json.loads((ROOT/'dependency-profile.json').read_text())
 packages=args.cache_dir.resolve()/'.lake/packages'
 env=dict(os.environ)
 env['LEAN_PATH']=os.pathsep.join([str(ROOT/'.lake/build/lib/lean')]+[str(packages/row['name']/'.lake/build/lib/lean') for row in profile['packages']])
 env['LEAN_NUM_THREADS']='1'
 env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 env['LEAN_SYSROOT']=str(prefix)
 env.pop('LEAN_CC',None)
 if args.compile_only:
  return subprocess.run([str(lean),'-R',str(work),'-j1','-M'+str(args.memory_mb),'-o',str(work/'CombinedCorrespondence.olean'),str(source)],cwd=work,env=env).returncode
 _,digest=inventory(ROOT)
 artifacts={}
 for module in (config['challenge_module'],config['solution_module']):
  stem=ROOT/'.lake/build/lib/lean'/Path(*module.split('.'))
  artifacts[module]=[{'path':str(path),'sha256':sha(path.read_bytes()),'bytes':path.stat().st_size} for path in (Path(str(stem)+ending) for ending in ['.olean','.olean.private','.olean.server','.ir','.ir.sig'])]
 native_compile_steps=[]
 phase_exit_codes=[]
 materializations=[]
 executable_digest=None
 c_digest=None
 def execute(command,out,err):
  try:return subprocess.run(command,cwd=work,env=env,stdout=out,stderr=err,timeout=args.timeout).returncode
  except subprocess.TimeoutExpired:
   err.write(b'\nDiagnostic subprocess exceeded its timeout and was terminated.\n')
   err.flush()
   return 124
 with (work/'stdout.txt').open('wb') as out,(work/'stderr.txt').open('wb') as err:
  compilation=[('emit-c',[str(lean),'-R',str(work),'-j1','-M'+str(args.memory_mb),'-c',str(cfile),str(source)]),('link-native',[str(leanc),'-O2',str(cfile),'-o',str(executable)])]
  for stage,command in compilation:
   print(json.dumps({'phase':stage,'status':'running'}),flush=True)
   code=execute(command,out,err)
   native_compile_steps.append({'stage':stage,'exit_code':code})
   print(json.dumps({'phase':stage,'exit_code':code}),flush=True)
   if code:break
  if len(native_compile_steps)==2 and all(row['exit_code']==0 for row in native_compile_steps):
   executable_digest=sha(executable.read_bytes())
   c_digest=sha(cfile.read_bytes())
   phases=[['materialize','Challenge',str(work/'challenge.constants')],['materialize','Solution',str(work/'solution.constants')],['compare',str(work/'challenge.constants'),str(work/'solution.constants')]]
   for phase in phases:
    print(json.dumps({'phase':phase[0],'module':phase[1] if phase[0]=='materialize' else None,'status':'running'}),flush=True)
    code=execute([str(executable),*phase],out,err)
    phase_exit_codes.append(code)
    print(json.dumps({'phase':phase[0],'module':phase[1] if phase[0]=='materialize' else None,'exit_code':code}),flush=True)
    if code:break
    if phase[0]=='materialize':
     path=Path(phase[2])
     materializations.append({'module':phase[1],'path':str(path),'sha256':sha(path.read_bytes()),'bytes':path.stat().st_size})
 _,after=inventory(ROOT)
 stable=after==digest
 artifacts_stable=all(Path(row['path']).is_file() and sha(Path(row['path']).read_bytes())==row['sha256'] for rows in artifacts.values() for row in rows)
 driver_stable=sha(Path(__file__).read_bytes())==driver_digest
 query_stable=source.is_file() and sha(source.read_bytes())==query_digest
 compiler_stable=lean.is_file() and sha(lean.read_bytes())==compiler_digest
 native_inputs_stable=all(Path(row['path']).is_file() and sha(Path(row['path']).read_bytes())==row['sha256'] for row in native_inputs.values())
 executable_stable=bool(executable_digest and executable.is_file() and sha(executable.read_bytes())==executable_digest)
 c_stable=bool(c_digest and cfile.is_file() and sha(cfile.read_bytes())==c_digest)
 materializations_stable=all(Path(row['path']).is_file() and sha(Path(row['path']).read_bytes())==row['sha256'] for row in materializations)
 stdout=(work/'stdout.txt').read_bytes()
 stderr=(work/'stderr.txt').read_bytes()
 details=None
 for line in stdout.decode('utf-8',errors='replace').splitlines():
  if line.startswith('CORRESPONDENCE '):details=json.loads(line[len('CORRESPONDENCE '):])
 passed=bool(len(phase_exit_codes)==3 and all(code==0 for code in phase_exit_codes) and stable and artifacts_stable and driver_stable and query_stable and compiler_stable and native_inputs_stable and executable_stable and c_stable and materializations_stable and details and details.get('status')=='pass' and details.get('selected_declarations_are_theorems'))
 last_code=phase_exit_codes[-1] if phase_exit_codes else native_compile_steps[-1]['exit_code']
 report={'schema_version':1,'kind':'lean-bundled-comparator-core','status':'pass' if passed else 'fail','comparison_passed':passed,'selected_declarations_are_theorems':bool(details and details.get('selected_declarations_are_theorems')),'source_inventory_sha256':digest,'source_stable':stable,'compiled_artifacts_stable':artifacts_stable,'driver_stable':driver_stable,'query_stable':query_stable,'compiler_stable':compiler_stable,'lake_library_path':str(lake_library),'lake_library_sha256':native_inputs['lake_static_library']['sha256'],'lake_library_stable':native_inputs_stable,'native_toolchain_inputs':native_inputs,'native_toolchain_inputs_stable':native_inputs_stable,'native_executable_sha256':executable_digest,'native_executable_stable':executable_stable,'generated_c_sha256':c_digest,'generated_c_stable':c_stable,'native_compile_steps':native_compile_steps,'statement_materializations':materializations,'statement_materializations_stable':materializations_stable,'comparator_config_sha256':sha(config_bytes),'compiler_version':version,'compiler_sha256':compiler_digest,'challenge_module':config['challenge_module'],'solution_module':config['solution_module'],'theorem_names':config['theorem_names'],'definition_names':[],'permitted_axioms':config['permitted_axioms'],'comparator_core':'Lake.Check.compareAt from pinned Lean 4.35.0','scope':'Local exact type/ordinary-body comparison using bundled compareAt. Temporary object compaction is distinct from standalone lean4export proof export, kernel replay or Palomar verification.','comparison_input':'independent compiled type/ordinary-value closures materialized as self-contained Lean CompactedRegions; selected theorem proof values omitted; exact exporter mdata/let-hint normalization; actual compareAt unchanged; native compilation changes execution only','details':details,'exit_code':last_code,'challenge_artifacts':artifacts[config['challenge_module']],'solution_artifacts':artifacts[config['solution_module']],'phase_exit_codes':phase_exit_codes,'expression_normalization':['erase_expr_mdata','normalize_let_nondep_false'],'normalization_source':'LeanExport.Basic.removeMData in pinned Lean 4.35.0','statement_materialization_performed':bool(materializations),'selected_proof_values_omitted':True,'proof_export_performed':False,'kernel_replay_performed':False,'nanoda_replay_performed':False,'official_palomar_verification':False,'driver_path':'scripts/check_combined_correspondence.py','driver_sha256':driver_digest}
 public=ROOT/'verification/correspondence'
 public.mkdir(parents=True,exist_ok=True)
 for role,name,data in [('query','query.txt',query.encode()),('stdout','stdout.txt',stdout),('stderr','stderr.txt',stderr)]:
  (public/name).write_bytes(data)
  report[role+'_path']=(public/name).relative_to(ROOT).as_posix()
  report[role+'_sha256']=sha(data)
 (ROOT/'verification/combined-correspondence.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
 print(json.dumps(report,indent=2))
 return 0 if passed else 1
if __name__=='__main__':raise SystemExit(main())
