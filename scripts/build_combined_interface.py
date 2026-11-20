"""Generate a single Palomar statement from preserved component interfaces."""
from __future__ import annotations
import argparse,hashlib,json,re,sys,textwrap
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from extract_semantic_surface import parse_module,theorem_type,resolve,IDENTIFIER,DECLARATIONS,PROOF
from stage_sources import source_mask
CACHE_RESET="reset_proof_cache"
CACHE_DEFINITION='local macro "reset_proof_cache" : command => `(run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {})\n'

def strip_comments(text):
    out=[];i=0;depth=0;string=False
    while i<len(text):
        pair=text[i:i+2]
        if depth:
            if pair=="/-":depth+=1;i+=2
            elif pair=="-/":depth-=1;i+=2
            else:
                if text[i]=="\n":out.append("\n")
                i+=1
        elif string:
            out.append(text[i])
            if text[i]=="\\" and i+1<len(text):out.append(text[i+1]);i+=2
            else:
                if text[i]=='"':string=False
                i+=1
        elif pair=="/-":out.append(" ");depth=1;i+=2
        elif pair=="--":
            end=text.find("\n",i);i=len(text) if end<0 else end
        else:
            out.append(text[i])
            if text[i]=='"':string=True
            i+=1
    if depth or string:raise ValueError("Unclosed comment/string")
    return "".join(out)

def compact(text):
    """Fold only layout-independent terms; preserve records/equation bodies."""
    text=strip_comments(text).strip()
    text=re.sub(r"(?m)^[ \t]*#(?:print|check)[^\n]*(?:\n|$)","",text)
    text="\n".join(x.rstrip() for x in text.splitlines() if x.strip())
    code=source_mask(text)
    sensitive=bool(re.search(r"\b(?:match|do|where|let)\b|(?m:^\s*\|)|\{[^{}]*:=",code,re.S))
    hole=bool(re.search(r":=\s*by\s+sorry\s*$",code))
    if not sensitive and '"' not in text and (hole or not re.search(r"\bby\b",code)):
        flat=re.sub(r"\s+"," ",text)
        return "\n".join(textwrap.wrap(flat,width=320,subsequent_indent="  ",break_long_words=False,break_on_hyphens=False))+"\n"
    # The first assignment in a where block belongs to a field, not its header.
    if match:=re.search(r"\bwhere\b",code):
        head=text[:match.start()]
        if not re.search(r"\b(?:by|match|do|let)\b",source_mask(head)):
            return re.sub(r"\s+"," ",head).rstrip()+" "+text[match.start():]+"\n"
        return text+"\n"
    if match:=re.search(r"(?m:^\s*\|)",code):
        head=text[:match.start()]
        if not re.search(r"\b(?:by|match|do|let)\b",source_mask(head)):
            return re.sub(r"\s+"," ",head).rstrip()+"\n"+text[match.start():]+"\n"
    depth=0
    for i,ch in enumerate(code[:-1]):
        if ch in "([{":depth+=1
        elif ch in ")]}":depth-=1
        elif code[i:i+2]==":=" and depth==0:
            head=text[:i]
            if not re.search(r"\b(?:let|match|do)\b",source_mask(head)) and '"' not in head:
                return re.sub(r"\s+"," ",head).rstrip()+" "+text[i:]+"\n"
            break
    return text+"\n"

def command_unit(commands):
    stack=[];unit=None;mapping={}
    for c in commands:
        if c.kind in ("section","namespace"):
            if not stack:unit=c.index
            stack.append(c.index)
        mapping[c.index]=unit
        if c.kind=="end" and stack:
            stack.pop()
            if not stack:unit=None
    return mapping


def statement_commands(row):
    """Preserve original source positions and genuine generated-declaration owners."""
    from extract_semantic_surface import COMMAND
    path=ROOT/row["project_path"]/"Challenge.lean"
    original=path.read_text(encoding="utf-8")
    commands=parse_module(row["id"],original.encode())["commands"]
    for command in commands:command.original_index=command.index
    if row["id"]!="TR-04":return commands
    proof_rel=row["project_path"]+"/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean"
    proof_text=(ROOT/proof_rel).read_text(encoding="utf-8")
    marker=original.index("/- Original module: NLA.TR04.LexicographicTensorReplayR3.PureDefinitions -/")
    start=original.rfind("section\n",0,marker)
    next_marker=original.index("/- Original module:",marker+10)
    stop=original.rfind("section\n",0,next_marker)
    body_start=proof_text.index("set_option autoImplicit false")
    header="section\n/- Original module: NLA.TR04.LexicographicTensorReplayR3.PureDefinitions -/\n"
    replacement=header+proof_text[body_start:]+"\nend\n"
    augmented=original[:start]+replacement+original[stop:]
    commands=parse_module(row["id"],augmented.encode())["commands"]
    def positions(text):
        return [m for m in COMMAND.finditer(source_mask(text)) if not
            (m.group("kind")=="section" and "expose" in m.group("attributes") and
             "public" in m.group("modifiers").split())]
    old_positions=positions(original);new_positions=positions(augmented)
    difference=len(new_positions)-len(old_positions)
    old_unit=next(i for i,m in enumerate(old_positions) if m.start()>=start)
    new_stop=start+len(replacement)
    for command in commands:
        position=new_positions[command.index].start()
        command.original_index=command.index if position<start else command.index-difference if position>=new_stop else old_unit
        if start+len(header)<=position<new_stop-len("\nend\n"):
            command.source_override={"path":proof_rel,"text":proof_text,"position":body_start+position-start-len(header)}
    return commands


def component_surface(row):
    p=ROOT/row["project_path"]
    config=json.loads((p/"comparator.json").read_text(encoding="utf-8"))
    commands=statement_commands(row)
    by={}
    for c in commands:
        if c.name:by.setdefault(c.name,[]).append(c)
    targets=set(config["theorem_names"]);queue=[]
    for name in config["theorem_names"]:
        matches=by.get(name,[])
        if len(matches)!=1:raise ValueError("Nonunique target "+name)
        queue.extend(matches)
    if row["id"]=="TR-04":
        for owner in ["Reference.LexTensorCompletion.svdFrame","Reference.LexTensorCompletion.feasible",
                      "Reference.LexOrderedTensorSolver.firstMinimum","Reference.LexOrderedTensorSolver.solver"]:
            queue.extend(by[owner])
    units=command_unit(commands);contexts={}
    for c in commands:
        if c.kind in ("instance","attribute","universe","variable","notation","infix","infixl","infixr","prefix","postfix"):
            contexts.setdefault(units[c.index],[]).append(c)
    queue.extend(c for c in commands if c.kind in ("notation","infix","infixl","infixr","prefix","postfix"))
    selected={};active=set()
    while queue:
        c=queue.pop()
        if c.key in selected:continue
        if c.private and c.kind in DECLARATIONS:raise ValueError("Private dependency "+str(c.name))
        selected[c.key]=c;unit=units[c.index]
        if unit not in active:active.add(unit);queue.extend(contexts.get(unit,[]))
        text=theorem_type(c) if c.kind in PROOF and c.name in targets else c.text
        for token in set(IDENTIFIER.findall(source_mask(text))):
            resolved=resolve(token,c,by)
            if "." in token and not token.startswith(("NLA.","Reference.","IV04.","Complexity.")):
                member=token.rsplit(".",1)[1]
                resolved=resolved+[x for name,items in by.items() if name.endswith("."+member) for x in items]
            queue.extend(x for x in resolved if x.key!=c.key)
    stack=[];pairs={};ancestors={}
    for c in commands:
        ancestors[c.index]=tuple(stack)
        if c.kind in ("namespace","section"):stack.append(c.index)
        elif c.kind=="end":pairs[stack.pop()]=c.index
    if stack:raise ValueError("Unclosed source scope")
    keep={c.index for c in selected.values()}
    for n in list(keep):
        for start in ancestors[n]:keep.add(start);keep.add(pairs[start])
    for c in commands:
        if units[c.index] in active and c.kind not in DECLARATIONS and c.kind not in ("namespace","section","end"):keep.add(c.index)
    return commands,keep,targets,config


def simplify_context(commands,keep):
    """Share code-generation setup; preserve every original declaration's option scope."""
    units=command_unit(commands);stack=[];ends={};original_auto=True;option_stack=[];true_units=set()
    for c in commands:
        if c.kind in ("namespace","section"):
            stack.append(c.index);option_stack.append(original_auto)
        elif c.kind=="end":
            ends[stack.pop()]=c.index;original_auto=option_stack.pop()
        elif c.kind=="set_option":
            match=re.match(r"set_option\s+autoImplicit\s+(false|true)\b",strip_comments(c.text).strip())
            if match:original_auto=match[1]=="true"
        if c.index in keep and c.kind in DECLARATIONS|{"variable","universe"} and original_auto:
            true_units.add(units[c.index])
    ordered=[c.index for c in commands if c.index in keep];following=dict(zip(ordered,ordered[1:]));by_index={c.index:c for c in commands}
    skip=set();replace={};after={}
    for c in commands:
        if c.index not in keep or c.kind!="section" or not strip_comments(c.text).strip().startswith("noncomputable section"):continue
        closing=ends[c.index];next_index=following.get(closing)
        if next_index is not None and by_index[next_index].kind=="end":
            skip.update((c.index,closing))
        else:replace[c.index]="section\n"
    emitted_auto=False;option_stack=[]
    for c in commands:
        if c.index not in keep or c.index in skip:continue
        if c.kind in ("namespace","section"):
            option_stack.append(emitted_auto)
            if c.index==units[c.index] and c.index in true_units:
                after[c.index]="set_option autoImplicit true\n";emitted_auto=True
        elif c.kind=="end":emitted_auto=option_stack.pop()
        elif c.kind=="set_option":
            match=re.match(r"set_option\s+autoImplicit\s+(false|true)\b",strip_comments(c.text).strip())
            if match:
                value=match[1]=="true"
                if value==emitted_auto:skip.add(c.index)
                emitted_auto=value
    if option_stack:raise ValueError("Unbalanced simplified context")
    return skip,replace,after


def fold_context(output):
    """Put adjacent simple source-context commands on shared header/footer lines."""
    result=[];pending=[]
    def flush():
        if pending:
            line=""
            for command in pending:
                if line and len(line)+1+len(command)>450:
                    result.append(line+"\n");line=""
                line=(line+" " if line else "")+command
            if line:result.append(line+"\n")
            pending.clear()
    for text in output:
        if len(text.splitlines())==1 and re.match(r"^(?:(?:noncomputable|public)\s+)?(?:namespace|section|end|set_option|open|attribute|variable|universe|reset_proof_cache)\b",text):
            pending.append(text.strip())
        else:
            flush();result.append(text)
    flush()
    return "".join(result)

def generate():
    index=json.loads((ROOT/"submission-index.json").read_text(encoding="utf-8"))
    components=index.get("components",index.get("entries"))
    if len(components)!=17:raise ValueError("Expected seventeen preserved components")
    pieces=["module\nimport all Lean.Meta.Match.Match\npublic import Mathlib\n@[expose] public section\nset_option autoImplicit false noncomputable section\n",CACHE_DEFINITION,
        "/-! Numerical Linear Algebra, Explained: twenty problem resolutions. Unchanged semantic definitions and theorem types from preserved components.\n"
        "Accounts and attribution: README.md, docs/COMBINED-DEFINITIONS.md, formalization.yaml and NOTICE.md.\n"
        "At 92 original source-module boundaries, only Lean's auxiliary-proof and matcher caches are cleared, preserving generated names;\n"
        "no declarations or assumptions change. -/\n"]
    imports=[];names=[];seen={};rows=[];duplicates=[]
    for row in components:
        commands,keep,targets,config=component_surface(row)
        names.extend(config["theorem_names"]);output=[];retained=[];units=command_unit(commands)
        context_skip,context_replace,context_after=simplify_context(commands,keep)
        if row["id"]=="TR-27":
            output.extend(["section\n","attribute [-instance] CommCStarAlgebra.toNormedCommRing NonUnitalCStarAlgebra.toNormedSpace\n"])
        for c in commands:
            if c.index not in keep or c.index in context_skip:continue
            if c.index==units.get(c.index) and c.kind=="section":output.append(CACHE_RESET+"\n")
            if c.kind in ("macro","elab","syntax","initialize","mutual"):raise ValueError("Unsupported syntax "+c.key)
            text=theorem_type(c)+" := by sorry\n" if c.kind in PROOF and c.name in targets else context_replace.get(c.index,c.text)
            if c.kind=="open":
                retained_names={x.name for x in commands if x.index in keep and x.name}
                def retain_open(match):
                    name=match.group(0)
                    return name if any(n==name or n.startswith(name+".") for n in retained_names) else ""
                text=re.sub(r"\b(?:NLA|Reference|IV04|Complexity)(?:\.[A-Za-z_][\w.]*)?",retain_open,text)
                if re.match(r"^open\s*(?:\n|$)",strip_comments(text)):continue
            if c.name and c.kind in DECLARATIONS:
                signature=strip_comments(text).strip()
                if c.name in seen:
                    if signature!=seen[c.name]:raise ValueError("Conflicting declaration "+c.name)
                    duplicates.append({"name":c.name,"component":row["id"]});continue
                seen[c.name]=signature;retained.append(c.name)
            output.append(compact(text))
            if c.index in context_after:output.append(context_after[c.index])
        if row["id"]=="TR-27":output.append("end\n")
        changed=True
        while changed:
            old=output;stack=[];remove=set()
            for i,t in enumerate(output):
                m=re.match(r"^(?:(?:noncomputable|public)\s+)?(namespace|section|end)\b",t)
                if not m:continue
                if m[1] in ("namespace","section"):stack.append(i)
                elif stack:
                    start=stack.pop()
                    harmless=lambda t:bool(re.match(r"^(?:open|set_option|universe|variable)\b",strip_comments(t).strip()))
                    if all(j in remove or harmless(output[j]) for j in range(start+1,i)):
                        remove.update(range(start,i+1))
            output=[t for i,t in enumerate(output) if i not in remove];changed=len(old)!=len(output)
        pieces.append("/- "+row["id"]+": "+row.get("title","")+". -/\n"+fold_context(output))
        # Only primary proof environments are co-imported. Alternative auxiliary
        # libraries remain preserved and independently compiled in the components.
        for target in row["targets"]:
            module=target["original_solution_module"]
            if module=="PaperSolution":module="NLA.Collection."+row["id"].replace("-","")+"PaperSolution"
            if module not in imports:imports.append(module)
        rows.append({"id":row["id"],"retained_named_declarations":retained,"theorem_names":config["theorem_names"]})
    challenge="".join(pieces)
    lines=len(challenge.splitlines());size=len(challenge.encode())
    if lines>1000 or size>100*1024:raise ValueError(f"Challenge too large: {lines} lines / {size} bytes")
    solution="module\n"+"".join("public import "+x+"\n" for x in imports)+"\n@[expose] public section\n"
    base_names=list(dict.fromkeys(names))
    support_path=ROOT/"audit/combined-supporting-theorems.json"
    support=json.loads(support_path.read_text(encoding="utf-8")) if support_path.is_file() else {"schema_version":1,"theorems":[]}
    if support.get("schema_version")!=1:raise ValueError("Unsupported auxiliary theorem manifest")
    helpers=[row["name"] for row in support["theorems"]]
    if len(set(base_names+helpers))!=len(base_names)+len(helpers):raise ValueError("Duplicate auxiliary theorem target")
    if any(name.startswith("_private.") for name in helpers):raise ValueError("Auxiliary targets must be public theorem names")
    config={"challenge_module":"Challenge","solution_module":"Solution","theorem_names":base_names+helpers,
        "definition_names":[],"enable_nanoda":True,"permitted_axioms":["propext","Classical.choice","Quot.sound"]}
    outputs={"Challenge.lean":challenge,"Solution.lean":solution,"comparator.json":json.dumps(config,indent=2)+"\n"}
    return outputs,{"challenge_lines":lines,"challenge_bytes":size,"selected_declarations":len(config["theorem_names"]),
        "components":rows,"deduplicated_declarations":duplicates,"solution_imports":imports}


def definition_index():
    """Index retained declarations and quote original documentation verbatim."""
    from extract_semantic_surface import COMMAND
    components=json.loads((ROOT/"submission-index.json").read_text(encoding="utf-8"))["components"]
    text=["# Combined statement definitions and declarations\n\n",
      "This index links every retained declaration to its preserved component source. "
      "The source definitions and selected theorem types remain in the root Challenge. "
      "Documentation blocks below are copied verbatim from the original component interfaces; "
      "no new mathematical interpretation is supplied for undocumented declarations. "
      "The component README files provide the informal accounts, hypotheses and limitations.\n"]
    seen=set();count=0;doc_count=0
    for row in components:
        original=(ROOT/row["project_path"]/"Challenge.lean").read_text(encoding="utf-8")
        commands,keep,targets,config=component_surface(row)
        matches=[m for m in COMMAND.finditer(source_mask(original)) if not
            (m.group("kind")=="section" and "expose" in m.group("attributes") and
             "public" in m.group("modifiers").split())]
        if len(matches)!=max(c.original_index for c in commands if not hasattr(c,"source_override"))+1:raise ValueError("Source location mapping changed: "+row["id"])
        text.append("\n## "+row["id"]+"\n")
        for c in commands:
            if c.index not in keep or c.kind not in DECLARATIONS:continue
            if c.name:
                if c.name in seen:continue
                seen.add(c.name)
            override=getattr(c,"source_override",None)
            document=override["text"] if override else original
            position=override["position"] if override else matches[c.original_index].start()
            line=document.count("\n",0,position)+1
            label=c.name or ("Unnamed "+c.kind+" in "+c.namespace+" (source line "+str(line)+")")
            text.append("\n### "+label+"\n")
            source="../"+(override["path"] if override else row["project_path"]+"/Challenge.lean")+"#L"+str(line)
            text.append("\n["+c.kind+" in preserved source]("+source+")\n")
            doc=re.search(r"/--((?:(?!/--).)*?)-/\s*$",document[:position],re.S)
            if doc:
                raw=doc.group(0).rstrip();fence=chr(96)*3
                while fence in raw:fence+=chr(96)
                text.append("\n"+fence+"lean\n"+raw+"\n"+fence+"\n");doc_count+=1
            count+=1
    text.insert(2,"\nIndexed declarations: "+str(count)+". Original documentation blocks: "+str(doc_count)+".\n")
    return "".join(text)


def declaration_origins():
    """Limited source-level provenance audit, independent of proof verification."""
    from collections import defaultdict
    from parallel_build import imports
    modules={}
    def visit(module):
        if module in modules:return
        path=ROOT/Path(*module.split(".")).with_suffix(".lean")
        if not path.is_file():return
        data=path.read_bytes();modules[module]=data
        for dependency in imports(data.decode("utf-8-sig")):visit(dependency)
    visit("Solution")
    components=json.loads((ROOT/"submission-index.json").read_text())["components"]
    wanted={};groups={}
    for row in components:
        commands,keep,targets,config=component_surface(row);units=command_unit(commands)
        for command in commands:
            if command.index not in keep or not command.name or command.kind not in DECLARATIONS or command.name in wanted:continue
            unit=units[command.index]
            marker=re.search(r"(?:Original|Source) module:\s*([^\s]+)",commands[unit].text if unit is not None else "")
            group=(row["id"],marker[1] if marker else str(unit))
            wanted[command.name]={"component":row["id"],"statement_unit":group[1]}
            groups.setdefault(group,[]).append(command.name)
    origins=defaultdict(list);errors=[]
    for module,data in sorted(modules.items()):
        text=re.sub(r"(?m)^set_option[^\r\n]*\bin[ \t]*$","",data.decode("utf-8-sig"))
        try:commands=parse_module(module,text.encode())["commands"]
        except Exception as error:errors.append({"module":module,"reason":str(error)});continue
        for command in commands:
            if command.name in wanted:origins[command.name].append({"module":module,"command_index":command.index})
    missing=sorted(set(wanted)-set(origins))
    if missing or any(len(v)!=1 for v in origins.values()):raise ValueError("Missing or nonunique source origins: "+repr(missing))
    module_groups=defaultdict(set);group_rows=[];order_failures=[]
    for group,names in sorted(groups.items()):
        actual={origins[name][0]["module"] for name in names}
        if len(actual)!=1:raise ValueError("Statement source unit mixes actual modules: "+repr(group))
        module=next(iter(actual));module_groups[module].add(group)
        positions=[origins[name][0]["command_index"] for name in names]
        if positions!=sorted(positions):order_failures.append(group)
        group_rows.append({"component":group[0],"statement_unit":group[1],"proof_module":module,"declarations":names})
    if order_failures:raise ValueError("Retained source order differs: "+repr(order_failures))
    if any(len(v)>1 for v in module_groups.values()):raise ValueError("An original module is split across statement units")
    source_rows=[{"module":m,"path":Path(*m.split(".")).with_suffix(".lean").as_posix(),"sha256":hashlib.sha256(data).hexdigest()} for m,data in sorted(modules.items())]
    digest=hashlib.sha256(json.dumps(source_rows,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    return {"schema_version":1,"kind":"source-level-declaration-origin-audit","scope":"Static source parser audit of retained named declarations and module/order boundaries; not a Lean or Comparator result.",
        "primary_graph_modules":len(modules),"retained_named_declarations":len(wanted),"all_retained_named_declarations_mapped":True,"within_module_order_preserved":True,
        "mixed_source_units":[],"split_original_modules":[],"unparsed_non_owner_modules":errors,"unparsed_module_scope":"These files own no retained named statement declaration; their proof validation remains covered by compilation.",
        "solution_sha256":hashlib.sha256((ROOT/"Solution.lean").read_bytes()).hexdigest(),"comparator_sha256":hashlib.sha256((ROOT/"comparator.json").read_bytes()).hexdigest(),
        "source_graph_sha256":digest,"source_modules":source_rows,"source_units":group_rows,
        "component_statement_inputs":[{"path":row["project_path"]+"/Challenge.lean","sha256":hashlib.sha256((ROOT/row["project_path"]/"Challenge.lean").read_bytes()).hexdigest()} for row in components],
        "retained_cache_owner":{"name":"Reference.LexTensorCompletion.svdFrame","source":"projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean","reason":"Retains original closed-proof cache ownership before frameRun without changing any selected theorem."},
        "retained_cache_owners":[{"name":name,"source":"projects/TR-04/NLA/TR04/LexicographicTensorReplayR3/PureDefinitions.lean","reason":reason} for name,reason in [
            ("Reference.LexTensorCompletion.svdFrame","Original auxiliary-proof owner used by frameRun."),
            ("Reference.LexTensorCompletion.feasible","Original matcher owner used by ttRun._unary."),
            ("Reference.LexOrderedTensorSolver.firstMinimum","Original matcher owner used by minimumRun._f."),
            ("Reference.LexOrderedTensorSolver.solver","Original matcher owner used by solverExecutionRun.")]],
        "context_setup":{"global_noncomputable_section":True,"autoImplicit_declaration_contexts_preserved":True,"removed_scopes":"Only redundant noncomputable scopes immediately followed by a closing enclosing scope; original source-unit and other local boundaries remain."}}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--check",action="store_true");p.add_argument("--audit-origins",action="store_true");args=p.parse_args()
    if args.audit_origins:
        report=declaration_origins();path=ROOT/"audit/combined-declaration-origins.json";data=(json.dumps(report,indent=2)+"\n").encode()
        if args.check:
            if not path.is_file() or path.read_bytes()!=data:raise SystemExit("Stale declaration-origin audit")
        else:path.write_bytes(data)
        print(json.dumps({k:v for k,v in report.items() if k not in {"source_modules","source_units","component_statement_inputs"}},indent=2));return
    outputs,report=generate()
    outputs["docs/COMBINED-DEFINITIONS.md"]=definition_index()
    for name,text in outputs.items():
        path=ROOT/name;data=text.encode()
        if args.check:
            if not path.is_file() or path.read_bytes()!=data:raise SystemExit("Stale combined interface: "+name)
        else:path.write_bytes(data)
    print(json.dumps(report,ensure_ascii=False,indent=2))
if __name__=="__main__":main()
