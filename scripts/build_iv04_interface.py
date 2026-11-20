#!/usr/bin/env python3
"""Prepare IV-02/IV-04 Challenge by explicit semantic declaration dependency closure.
The generator preserves selected declaration syntax/types/bodies and original
namespace contexts. Output remains static until a successful Lean build.
"""
from __future__ import annotations
import argparse,collections,json,re,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from build_entry_interfaces import read_inputs, module_closure, module_key, body_without_header, scope_closures
from stage_sources import ROOT, load_json, source_mask, sha256, write_json

PROJECT='IV-04'
DOCSTRINGS={
 'IV04.Paper.Computational.firstBit':'The first output bit, with false for an empty word.',
 'IV04.Paper.Mat':'Real square matrices of order n.',
 'IV04.Paper.readUnary':'Read true bits up to a false terminator, returning their count and the unused suffix.',
 'IV04.Paper.readNatural':'Read a unary payload length and that many least-significant-first binary digits.',
 'IV04.Paper.rationalCode':'Encode a rational by its sign, absolute numerator and positive denominator.',
 'IV04.Paper.readRational':'Read sign, numerator and denominator fields using rational division, with the unused suffix.',
 'IV04.Paper.Computational.rationalDenseEndpointAll':'Check that both row-major endpoint tables vanish outside the three central diagonals.',
 'IV04.Paper.Computational.boxLowerReal':'The real lower endpoint at row-major index i*n+j, using zero as the list default.',
 'IV04.Paper.Computational.boxUpperReal':'The real upper endpoint at row-major index i*n+j, using zero as the list default.',
 'IV04.Paper.positiveCornerRhs':'The fixed right-hand side minus the last coordinate vector.',
 'IV04.Paper.positiveSolutions':'The union of solution sets A*x = -e_last over matrices A in S.',
 'IV04.Paper.Computational.NPHardOutputTask':'Every NP language has a polynomial-time one-query reduction to this exact output relation.',
 'IV04.Paper.Computational.regularUnitMatrixDeterminantDecisionLanguage':'The determinant threshold language restricted to the regular unit-superdiagonal promise.',
 'IV04.Paper.Computational.RegularUnitDeterminantRangeOutput':'Exact determinant-range output on a matrix satisfying the regular unit-superdiagonal promise.',
}
DECL_START=re.compile(r"^[ \t]*(?:(?:@\[[^\]]*\])\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped|public|nonrec)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|namespace|section|mutual|end|open|set_option|attribute|variable|universe|notation|macro|elab|syntax|initialize|example|export|infix|infixl|infixr|prefix|postfix)\b([^\r\n]*)",re.M)
IDENT=re.compile(r"[A-Za-z_\u0370-\u03ff][\w'.₀-₉]*(?:\.[A-Za-z_\u0370-\u03ff][\w'.₀-₉]*)*")
SEMANTIC={'def','abbrev','structure','inductive','class','instance','notation','macro','elab','syntax','initialize','export','deriving','infix','infixl','infixr','prefix','postfix'}
class Command:
 def __init__(self,module,index,kind,rest,body,namespace):
  self.module,self.index,self.kind,self.rest,self.body,self.namespace=module,index,kind,rest,body,namespace
  self.name=rest.split()[0] if rest.split() else ''
  self.fullname=(namespace+'.' if namespace else '')+self.name
  if self.name.startswith('_root_.'):self.fullname=self.name[7:]
  self.private=bool(re.match(r'(?:@\[[^\]]*\]\s*)?private\b',source_mask(body)))
 def label(self):return self.fullname if self.kind in SEMANTIC|{'theorem','lemma'} else self.kind+' '+self.rest

def parse_module(module,body):
 clean=source_mask(body);matches=list(DECL_START.finditer(clean));commands=[];scopes=[]
 for index,match in enumerate(matches):
  kind,rest=match.group(1),match.group(2).strip();finish=matches[index+1].start() if index+1<len(matches) else len(body)
  namespace='.'.join(name for sk,name in scopes if sk=='namespace')
  command=Command(module,index,kind,rest,body[match.start():finish],namespace)
  before=body[:match.start()];ds=before.rfind('/--');de=before.rfind('-/')
  command.doc=before[ds:de+2] if ds>=0 and de>ds and not before[de+2:].strip() else ''
  commands.append(command)
  if kind in {'namespace','section','mutual'}:scopes.append((kind,rest.split()[0] if rest else ''))
  elif kind=='end':
   name=rest.split()[0] if rest else ''
   if not scopes:raise ValueError('unmatched end '+module+':'+name)
   if not name:scopes.pop()
   else:
    where=next((i for i in range(len(scopes)-1,-1,-1) if scopes[i][1]==name),None)
    if where is None:raise ValueError('unmatched named end '+module+':'+name)
    del scopes[where:]
 return commands


def strip_comments(text):
 """Remove nested comments while preserving strings and source indentation."""
 out=[];i=0;depth=0;quoted=False;escape=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif quoted:
   char=text[i];out.append(char);i+=1
   if escape:escape=False
   elif char=='\\':escape=True
   elif char=='"':quoted=False
  elif text.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif text.startswith('--',i):
   end=text.find('\n',i);end=len(text) if end<0 else end
   out.extend(' '*(end-i));i=end
  else:
   char=text[i];out.append(char);i+=1
   if char=='"':quoted=True
 if depth:raise ValueError('Unclosed copied source comment')
 return ''.join(out)


def compact_code(text):
 code=strip_comments(text)
 return '\n'.join(line.rstrip() for line in code.splitlines() if line.strip())+'\n'


def emit_interface(entry,sources,ordered,modules,kept,result):
 needed={(c.module,c.index) for c in kept}
 if any(c.private for c in kept):raise ValueError('Private declaration requires an explicit public-name review')
 if result['ambiguities']:raise ValueError('Unresolved declaration-name ambiguity')
 pieces=['module\n\npublic import Mathlib\n\n@[expose] public section\n\n/-!\n# Exact interval-matrix complexity claims\n\nThe first theorem gives NP-completeness of determinant threshold decision and\nNP-hardness of exact determinant-range output on the specified rational\ntridiagonal interval matrices. The second gives NP-hardness of the full solution\nhull output. The definitions below retain the original binary encodings,\nmachine model, polynomial-time reductions and real interval semantics.\nThe corresponding Solution imports the complete proved development.\n-/\n']
 notices=[]
 for mod in ordered:
  if not any(c.module==mod for c in kept):continue
  original=sources[module_key(PROJECT,mod)].decode('utf-8-sig')
  for notice in re.findall(r'/-(?![!-])(?:(?!-/)[\s\S])*Copyright(?:(?!-/)[\s\S])*-/',original):
   if notice not in notices:notices.append(notice)
 pieces.extend(notices)
 omitted_open=[];records=[]
 for mod in ordered:
  if not any(c.module==mod for c in kept):continue
  block=['section\n','/- Source module: '+mod+' -/\n']
  for cmd in modules[mod]:
   if (cmd.module,cmd.index) in needed:
    if cmd.doc:block.append(cmd.doc+'\n')
    elif cmd.fullname in DOCSTRINGS:block.append('/-- '+DOCSTRINGS[cmd.fullname]+' -/\n')
    code=compact_code(cmd.body)
    if cmd.kind in {'theorem','lemma'} and cmd.fullname not in {n for t in entry['targets'] for n in t['theorem_names']}:
     # Such a helper is a separately compared theorem, never a semantic hole.
     if ':=' not in code:raise ValueError('Unsupported helper theorem without proof separator')
     code=code.split(':=',1)[0]+':= by sorry\n'
    block.append(code)
    records.append({'module':mod,'kind':cmd.kind,'name':cmd.fullname,'source_command_sha256':sha256(cmd.body.encode()),'source_doc_sha256':sha256(cmd.doc.encode()),'added_docstring':DOCSTRINGS.get(cmd.fullname) if not cmd.doc else None,'copied_code_sha256':sha256(code.encode())})
   elif cmd.kind in {'namespace','section','mutual','end','open','set_option','attribute','variable','universe'}:
    code=compact_code(cmd.body).splitlines()[0]+'\n'
    if cmd.kind=='open' and 'SATReduction' in code:
     omitted_open.append({'module':mod,'original':code.strip(),'reason':'No retained statement or semantic declaration uses the SAT-reduction implementation namespace.'})
     code=code.replace(' SATReduction','').replace('open IV04.Paper.Computational.SATReduction','').strip()+'\n'
     if code.strip()=='open' or not code.strip():continue
    block.append(code)
  body=''.join(block[1:])
  block.extend(x+'\n' for x in scope_closures(body))
  block.append('end\n')
  pieces.append(''.join(block))
 challenge='\n'.join(pieces).encode()
 if len(challenge.splitlines())>1000 or len(challenge)>102400:raise ValueError('Compact interval Challenge exceeds Palomar cap')
 from build_entry_interfaces import imports
 if imports(challenge)!=['Mathlib']:raise ValueError('Challenge import surface is not solely Mathlib')
 if re.search(r'\b(?:LeanCert|leancert)\b|#assert_trust',source_mask(challenge.decode())):raise ValueError('Forbidden statement utility declaration')
 # Reparse the final surface in its new module context and compare every
 # retained mathematical command, including literal notation strings and proof
 # subterms, after only comment/blank-line removal. This is a source identity
 # check; compilation and exported-expression identity remain separate.
 reparsed=parse_module('Challenge',body_without_header(challenge))
 original_code=[(c.kind,c.fullname,compact_code(c.body)) for c in kept]
 output_code=[(c.kind,c.fullname,compact_code(c.body)) for c in reparsed if c.kind in SEMANTIC|{'theorem','lemma'}]
 if original_code!=output_code:
  mismatch=next(((a,b) for a,b in zip(original_code,output_code) if a!=b),None)
  raise ValueError('Copied mathematical command identity mismatch: '+repr(mismatch))
 theorem_names=[c.fullname for c in kept if c.kind in {'theorem','lemma'}]
 if len(re.findall(r'\bsorry\b',source_mask(challenge.decode())))!=len(theorem_names):raise ValueError('Unexpected Challenge proof hole')
 architecture=load_json(ROOT/'docs/build-architecture.json')
 proof_roots=next(x['roots'] for x in architecture['minimum_claim_proof_closure']['projects'] if x['project']==PROJECT)
 import_roots=list(dict.fromkeys(target['original_solution_module'] for target in entry['targets']))
 solution=('module\n\n'+''.join('public import '+mod+'\n' for mod in import_roots)+'\n@[expose] public section\n\n/- The imports provide the original primary IV-02/IV-04 proof environment.\nEvery mapped auxiliary proof root is compiled independently by the full-source\nbuild; unrelated development environments need not share declaration names. -/\n').encode()
 config={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':theorem_names,'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound'],'enable_nanoda':True}
 outputs={f'projects/{PROJECT}/Challenge.lean':challenge,f'projects/{PROJECT}/Solution.lean':solution,f'projects/{PROJECT}/comparator.json':(json.dumps(config,indent=2)+'\n').encode()}
 for rel,data in outputs.items():(ROOT/rel).write_bytes(data)
 record={'id':PROJECT,'status':'generated-static; ordinary Lean build and official Palomar verification remain outstanding','mode':'original-module-visible identifier, constructor, notation and instance closure; semantic command bodies and headline theorem types copied unchanged','challenge_lines':len(challenge.splitlines()),'challenge_bytes':len(challenge),'challenge_direct_imports':['Mathlib'],'theorem_names':theorem_names,'solution_proof_roots':proof_roots,'solution_import_roots':import_roots,'independently_built_proof_roots':proof_roots,'retained_command_count':len(kept),'mathematical_command_source_identity':'pass; every retained type/body/notation command reparsed and text-identical after removing comments and blank lines','source_modules':[{ 'module':mod,'original_path':module_key(PROJECT,mod),'original_sha256':sha256(sources[module_key(PROJECT,mod)])} for mod in ordered if any(c.module==mod for c in kept)],'retained_commands':records,'omitted_implementation_namespace_opens':omitted_open,'unresolved_name_ambiguities':result['ambiguities'],'private_retained_declarations':[],'outputs':[{'path':rel,'sha256':sha256(data),'bytes':len(data)} for rel,data in outputs.items()],'generator_sha256':sha256(Path(__file__).read_bytes())}
 write_json(ROOT/'audit/iv04-interface.json',record)
 shared_path=ROOT/'audit/entry-interfaces.json'
 if shared_path.exists():
  shared=load_json(shared_path)
  shared['entries']=[row for row in shared['entries'] if row['id']!=PROJECT]+[record]
  shared['entries'].sort(key=lambda row:row['id'])
  write_json(shared_path,shared)
  from build_entry_interfaces import refresh_entry_inventory
  refresh_entry_inventory(shared['entries'])
 print(json.dumps({k:record[k] for k in ('id','status','challenge_lines','challenge_bytes','theorem_names')},indent=2))

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');args=parser.parse_args()
 sources=read_inputs();entry=next(x for x in load_json(ROOT/'primary-entry-targets.json')['entries'] if x['id']==PROJECT)
 roots=[x['original_challenge_module'] for x in entry['targets']]
 ordered=[];external=set();visited=set();ancestors={}
 def visit(module):
  if module in visited:return
  visited.add(module)
  key=module_key(PROJECT,module)
  if key not in sources:
   external.add(module);return
  from build_entry_interfaces import imports
  deps=imports(sources[key])
  for dependency in deps:visit(dependency)
  ancestors[module]=set(deps).union(*(ancestors.get(d,set()) for d in deps))
  ordered.append(module)
 for module in roots:visit(module)
 modules={mod:parse_module(mod,body_without_header(sources[module_key(PROJECT,mod)])) for mod in ordered}
 all_commands=[c for commands in modules.values() for c in commands]
 declarations=[c for c in all_commands if c.kind in SEMANTIC|{'theorem','lemma'}]
 short=collections.defaultdict(list);full=collections.defaultdict(list)
 for cmd in declarations:
  if cmd.name:short[cmd.name].append(cmd);full[cmd.fullname].append(cmd)
 selected_names={n for t in entry['targets'] for n in t['theorem_names']}
 selected=[c for c in declarations if c.fullname in selected_names]
 seen=set();queue=list(selected);ambiguities={};edges=collections.defaultdict(list)
 while queue:
  cmd=queue.pop()
  if (cmd.module,cmd.index) in seen:continue
  seen.add((cmd.module,cmd.index))
  # All references in definition values/types matter. Selected/helper theorem
  # proofs are intentionally omitted; only their unchanged types are followed.
  text=re.sub(r'@\[[^\]]*\]','',source_mask(cmd.body))
  if cmd.kind in {'theorem','lemma'}:
   text=re.split(r':=',text,maxsplit=1)[0]
  local_types={}
  for binder in re.finditer(r'[({]\s*([^(){}\n:]+?)\s*:\s*([\w.]+)',text):
   names=binder.group(1).split();typ=IDENT.findall(binder.group(2))
   if all(re.fullmatch(r"[A-Za-z_][\w']*",n) for n in names):
    for n in names:local_types[n]=typ[0] if typ else ''
  local_names=set(local_types)
  local_names.update(re.findall(r"[∀∃]\s*([A-Za-z_][\w']*)",text))
  for bind in re.findall(r"[∀∃]\s*((?:[A-Za-z_][\w']*\s+)*[A-Za-z_][\w']*)\s*[,∈:≤]",text):local_names.update(bind.split())
  local_names.update(re.findall(r"\{\s*([A-Za-z_][\w']*)\s*\|",text))
  for bind in re.findall(r"\blet\s*\(([\w,\s]+)\)\s*(?:←|:=)",text):local_names.update(x.strip() for x in bind.split(','))
  local_names.update(re.findall(r"\blet\s+([A-Za-z_][\w']*)\b",text))
  for binder in re.findall(r'\bfun\s+([A-Za-z_][\w\s\']*)\s*=>',text):local_names.update(binder.split())
  # Preserve instance data for retained semantic types. The typeclass solution
  # chosen while elaborating a copied body is part of its exact kernel term.
  if cmd.kind in {'structure','inductive','class'}:
   for instance in declarations:
    if instance.kind!='instance' or instance.module!=cmd.module:continue
    prefix=re.split(r':=|\bwhere\b',source_mask(instance.body),maxsplit=1)[0]
    if re.search(r'(?<![\w.])'+re.escape(cmd.name)+r'(?![\w])',prefix):queue.append(instance)
  # Preserve custom operator meanings, whose printed tokens are not identifiers.
  for notation in declarations:
   if notation.kind not in {'notation','infix','infixl','infixr','prefix','postfix'}:continue
   tokens=[s.strip() for s in re.findall(r'"([^"\n]+)"',notation.body)]
   if any(token and token in text for token in tokens):queue.append(notation)
  def visible(items):return [x for x in items if x.module==cmd.module or x.module in ancestors[cmd.module]]
  for name in IDENT.findall(text):
   if name in local_names:continue
   components=name.split('.');receiver=components[0]
   candidates=[]
   if len(components)>1 and receiver in local_names:
    typ=local_types.get(receiver,'').rsplit('.',1)[-1]
    if typ in {'List','Option','Bool','Nat','Fin','Matrix','Set','String','ℕ','ℚ','ℝ'}:continue
    if typ:
     wanted='.'.join([typ]+components[1:])
     candidates=visible([x for x in declarations if x.fullname.endswith('.'+wanted) or x.fullname==wanted])
   if not candidates:
    # Generated constructors/projections refer back to their parent declaration.
    for count in range(len(components),0,-1):
     partial='.'.join(components[:count])
     candidates=visible(full.get(partial,[]))
     if not candidates:
      pieces=cmd.namespace.split('.') if cmd.namespace else []
      for i in range(len(pieces),-1,-1):
       q='.'.join(pieces[:i]+[partial])
       if visible(full.get(q,[])):candidates=visible(full[q]);break
     if candidates:break
   if not candidates:
    key=name.rsplit('.',1)[-1];candidates=visible(short.get(key,[]))
    if len(candidates)>1:ambiguities[(cmd.fullname,name)]=[x.fullname for x in candidates]
   for target in candidates:
    queue.append(target);edges[target.fullname].append({'from':cmd.fullname,'reference':name})
 kept=[c for c in all_commands if (c.module,c.index) in seen]
 result={'module_count':len(ordered),'all_commands':len(all_commands),'declarations':len(declarations),'selected':[x.fullname for x in selected],'kept_count':len(kept),'kept_semantic_count':sum(c.kind in SEMANTIC for c in kept),'kept_theorem_count':sum(c.kind in {'theorem','lemma'} for c in kept),'kept_lines':sum(len(c.body.splitlines()) for c in kept),'kept_modules':len(set(c.module for c in kept)),'ambiguities':[{'from':a,'reference':b,'candidates':v} for (a,b),v in ambiguities.items()],'kept':[{'module':c.module,'kind':c.kind,'name':c.fullname,'private':c.private,'lines':len(c.body.splitlines())} for c in kept]}
 result['dependency_edges']=dict(edges)
 result['module_contexts']={mod:[{'kind':c.kind,'text':c.body.strip()} for c in modules[mod] if c.kind not in SEMANTIC|{'theorem','lemma','example'}] for mod in modules if any(c.module==mod for c in kept)}
 write_json(ROOT/'audit/iv04-semantic-pruning-analysis.json',result)
 print(json.dumps({k:v for k,v in result.items() if k not in {'kept','ambiguities','module_contexts','dependency_edges'}},indent=2))
 print('ambiguities',len(ambiguities))
 if args.write:emit_interface(entry,sources,ordered,modules,kept,result)
if __name__=='__main__':main()
