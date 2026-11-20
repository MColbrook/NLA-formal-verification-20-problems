#!/usr/bin/env python3
"""Conservatively prune declaration dependencies for large Challenge surfaces.

Every retained ordinary definition body and theorem type is copied from the
archived source. Genuine public helper theorems needed by those bodies become
explicit additional comparison targets. This does not check Lean elaboration.
Ambiguous identifier resolutions are recorded and conservatively include every
candidate; unresolved project-qualified names and private dependencies fail.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re

from stage_sources import ROOT, load_json, write_json, sha256, source_mask
from build_entry_interfaces import (PRIMARY, INTERFACES, read_inputs, module_key,
    imports, body_without_header, scope_closures, REVIEWED_UNUSED_UTILITY_IMPORTS,
    module_closure, neutralize_doc_comments, space_plain_relations, apply_interface_overrides, solution_import_roots, refresh_entry_inventory)

# Reviewed utility modules contribute only optional checking commands to these
# original statement closures. Mathematical declarations are resolved separately.
REVIEWED_UNUSED_UTILITY_IMPORTS.update({
    "TR-27": {"LeanCert.Tactic.Verification"},
    "TR-04": {"LeanCert.Tactic"},
    "MD-06": {"LeanCert.Tactic", "LeanCert.Tactic.Verification"},
})

KINDS = "theorem|lemma|def|abbrev|structure|inductive|class|instance|namespace|section|end|open|set_option|attribute|variable|universe|notation|macro|elab|syntax|initialize|example|export|deriving|infixl|infixr|infix|prefix|postfix|include|omit|mutual"
COMMAND = re.compile(r"^(?P<attributes>(?:@\[[^\]\r\n]*\][ \t]*(?:\r?\n[ \t]*)?)*)"
    r"(?P<modifiers>(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped|public)[ \t]+)*)"
    r"(?P<kind>" + KINDS + r")\b(?P<rest>[^\r\n]*)", re.M)
DECLARATIONS = {"theorem", "lemma", "def", "abbrev", "structure", "inductive", "class", "instance", "example"}
SEMANTIC = {"def", "abbrev", "structure", "inductive", "class", "instance"}
PROOF = {"theorem", "lemma"}
IDENTIFIER = re.compile(r"(?:[^\W\d]|_)[\w']*(?:\.(?:[^\W\d]|_)[\w']*)*")
PROJECT_PREFIXES = ("NLA.", "Reference.", "IV04.", "Complexity.")


@dataclass
class Command:
    module: str
    index: int
    kind: str
    name: str | None
    namespace: str
    opened: tuple[str, ...]
    text: str
    private: bool
    modifiers: str

    @property
    def key(self):
        return f"{self.module}#{self.index}"


def theorem_type(command: Command) -> str:
    """Find the top-level proof assignment, skipping let assignments in types."""
    clean = source_mask(command.text)
    depth = 0
    for i, char in enumerate(clean[:-1]):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and clean[i:i+2] == ":=" and depth == 0:
            before = clean[:i]
            # A theorem type may contain a let-bound object. Its assignment is
            # part of the exact type, rather than the proof assignment.
            line = before.rsplit("\n", 1)[-1]
            if re.search(r"\blet\s+[\w']+(?:\s*:[^=]*)?\s*$", line):
                continue
            return command.text[:i].rstrip()
    raise ValueError(f"Cannot identify exact theorem type for {command.name or command.key}")


def parse_module(module: str, data: bytes):
    body = body_without_header(data)
    clean = source_mask(body)
    if re.search(r"^set_option\b[^\r\n]*\bin\s*$", clean, re.M):
        raise ValueError(f"Scoped set_option requires explicit parser support: {module}")
    matches = list(COMMAND.finditer(clean))
    if not matches:
        raise ValueError(f"No recognized commands in {module}")
    commands, scopes, namespace, opened = [], [], "", []
    for index, match in enumerate(matches):
        kind, rest = match.group("kind"), match.group("rest").strip()
        finish = matches[index+1].start() if index+1 < len(matches) else len(body)
        text = body[match.start():finish]
        name = None
        if kind in DECLARATIONS and kind != "example":
            first = re.match(r"([A-Za-z_\u00c0-\uffff][\w'.\u00c0-\uffff]*)", rest)
            if first:
                short = first.group(1)
                name = (namespace + "." if namespace else "") + short
        command = Command(module, index, kind, name, namespace, tuple(opened), text,
            "private" in match.group("modifiers").split(), match.group("modifiers"))
        commands.append(command)
        if kind in ("namespace", "section"):
            label = rest.split()[0] if rest else ""
            scopes.append((kind, label, namespace, len(opened)))
            if kind == "namespace":
                namespace = (namespace + "." if namespace else "") + label
        elif kind == "end":
            label = rest.split()[0] if rest else ""
            if not scopes:
                raise ValueError(f"Unmatched end in {module}")
            if label:
                pos = next((i for i in range(len(scopes)-1, -1, -1) if scopes[i][1] == label), None)
                if pos is None:
                    raise ValueError(f"Unmatched named end {label} in {module}")
            else:
                pos = len(scopes)-1
            _, _, namespace, opened_length = scopes[pos]
            opened = opened[:opened_length]
            del scopes[pos:]
        elif kind == "open" and not rest.startswith("scoped "):
            # Preserve all actual source contexts in output; this conservative
            # identifier resolver uses simple opened namespace names only.
            opened += re.findall(r"[A-Za-z_][\w.]*", rest.split("(")[0])
    return {"module": module, "prefix": body[:matches[0].start()], "commands": commands}


def resolve(token: str, command: Command, by_name):
    # Generated constructors/projections belong to their defining structure or
    # inductive type; select that parent declaration without guessing a body.
    def exact_or_parent(name):
        test = name
        while test:
            if test in by_name:
                return by_name[test]
            if "." not in test:
                break
            test = test.rsplit(".", 1)[0]
        return []
    if token.startswith("_root_."):
        return exact_or_parent(token[7:])
    if token.startswith(PROJECT_PREFIXES):
        return exact_or_parent(token)
    # A generated-parent fallback must not swallow receiver methods. For
    # example, resolving X.cone inside ProjectiveVariety would otherwise stop
    # at the ProjectiveVariety structure before considering its cone method.
    receiver_candidates = []
    if "." in token:
        member = token.split(".", 1)[1]
        receiver_candidates = [x for name, values in by_name.items()
            if name == member or name.endswith("." + member) for x in values]
    namespace = command.namespace
    while True:
        candidate = (namespace + "." if namespace else "") + token
        found = exact_or_parent(candidate)
        if found:
            if candidate not in by_name and receiver_candidates:
                return receiver_candidates
            return found
        if not namespace:
            break
        namespace = namespace.rsplit(".", 1)[0] if "." in namespace else ""
    found = []
    for opened in command.opened:
        found += exact_or_parent(opened + "." + token)
    if found:
        return list({x.key: x for x in found}.values())
    # A suffix match conservatively catches declarations made visible by open
    # commands with unsupported syntax. Ambiguities are explicitly recorded.
    suffix = "." + token
    candidates = [x for name, values in by_name.items() if name == token or name.endswith(suffix) for x in values]
    if candidates:
        return candidates
    # Receiver-dot notation, e.g. X.zariskiClosure, refers to a method in
    # the receiver type namespace rather than to a namespace named X.
    if "." in token:
        member = token.split(".", 1)[1]
        suffix = "." + member
        return [x for name, values in by_name.items() if name == member or name.endswith(suffix) for x in values]
    return []


def build(entry: dict, sources, force: bool):
    project = entry["id"]
    primary_names = list(dict.fromkeys(name for target in entry["targets"] for name in target["theorem_names"]))
    root_modules = list(dict.fromkeys(target["original_challenge_module"] for target in entry["targets"]))
    ordered, external = module_closure(project, root_modules, sources)
    parsed = {module: parse_module(module, sources[module_key(project, module)]) for module in ordered}
    all_commands = [command for module in ordered for command in parsed[module]["commands"]]
    by_name = {}
    for command in all_commands:
        if command.name:
            by_name.setdefault(command.name, []).append(command)
    roots = []
    for name in primary_names:
        possible = [command for command in by_name.get(name, []) if command.module in root_modules]
        if len(possible) != 1:
            raise ValueError(f"Primary target not uniquely identified: {name}")
        roots.append(possible[0])
    selected, active_modules, queue, ambiguities, unresolved = {}, set(), roots[:], [], []
    def add_context(module):
        if module in active_modules:
            return
        active_modules.add(module)
        # Instances and notation/attribute contexts can affect elaboration
        # implicitly; retain them conservatively in every selected source module.
        for command in parsed[module]["commands"]:
            if command.kind in ("instance", "notation", "macro", "elab", "syntax", "initialize", "export", "infixl", "infixr", "infix", "prefix", "postfix", "attribute", "variable", "universe"):
                queue.append(command)
    while queue:
        command = queue.pop()
        if command.key in selected:
            continue
        selected[command.key] = command
        add_context(command.module)
        if command.private and command.kind in DECLARATIONS:
            raise ValueError(f"Private dependency needs an explicit stable-name bridge: {command.module}: {command.name}")
        if command.kind in PROOF:
            dependency_text = theorem_type(command)
        else:
            dependency_text = command.text
        clean = source_mask(dependency_text)
        # Remove each declaration's own name from the token stream to avoid
        # treating an otherwise harmless self reference as an ambiguity.
        for token in set(IDENTIFIER.findall(clean)):
            if token in {"namespace", "section", "end", "open", "scoped"}:
                continue
            resolved = resolve(token, command, by_name)
            if token.startswith(PROJECT_PREFIXES) and not resolved:
                # Open namespace names need no defining declaration of their own.
                if command.kind not in ("open", "namespace"):
                    unresolved.append({"from": command.name or command.key, "token": token})
            if len(resolved) > 1:
                ambiguities.append({"from": command.name or command.key, "token": token, "included_candidates": [x.name or x.key for x in resolved]})
            queue.extend(x for x in resolved if x.key != command.key)
    # Qualified names of local binders and namespace identifiers can be false
    # positives. Do not erase them or invent definitions; stop for inspection.
    if unresolved:
        write_json(ROOT / "audit" / "extraction-diagnostics" / f"{project}.json", {"id": project, "status": "blocked-unresolved-project-qualified-identifiers", "unresolved": unresolved, "ambiguities": ambiguities})
        raise ValueError(f"{project} has unresolved project-qualified identifiers; inspect extraction diagnostics")
    selected_names = {command.name for command in selected.values() if command.name}
    supporting = [command for command in all_commands if command.key in selected and command.kind in PROOF and command.name not in primary_names]
    supporting_names = list(dict.fromkeys(command.name for command in supporting))
    all_names = primary_names + supporting_names
    pieces = ["module\npublic import Mathlib\n@[expose] public section\n/-! Standalone exact statement and semantic-definition surface for " + ", ".join(entry["problem_ids"]) + ".\nEvery helper theorem placeholder is explicitly compared and genuinely proved on the Solution side. -/\n"]
    records = []
    for module in ordered:
        data = parsed[module]
        used = [command for command in data["commands"] if command.key in selected]
        if not used:
            continue
        body = data["prefix"]
        rendered = []
        for command in data["commands"]:
            keep = command.key in selected
            context = command.kind not in DECLARATIONS
            if not keep and not context:
                continue
            if command.kind in ("macro", "elab", "syntax", "initialize", "mutual"):
                raise ValueError(f"Unsupported metaprogramming or mutual command in pruned surface: {module}: {command.kind}")
            if command.kind in PROOF:
                text = space_plain_relations(theorem_type(command)) + " := by sorry\n"
                role = "primary theorem" if command.name in primary_names else "supporting theorem: exact well-definedness or construction certificate required by a retained semantic definition/type"
            else:
                text = command.text
                if command.kind == "open":
                    # An omitted namespace contributes no retained declarations.
                    # Drop only those project namespace tokens from open lists;
                    # canonical-library opens and all source scopes are retained.
                    def keep_open(match):
                        token = match.group(0)
                        if token.startswith(PROJECT_PREFIXES) and not any(name == token or name.startswith(token + ".") for name in selected_names):
                            return ""
                        return token
                    text = re.sub(r"(?:NLA|Reference|IV04|Complexity)\.[A-Za-z_][\w.]*", keep_open, text)
                    if re.match(r"^open[ \t]*(?:\r?\n|$)", text):
                        text = "\n"
                role = "exact semantic declaration" if command.kind in SEMANTIC else "source context"
            body += text
            if command.kind in DECLARATIONS:
                rendered.append({"name": command.name, "kind": command.kind, "role": role, "source_command_sha256": sha256(command.text.encode("utf-8")), "retained_type_or_body_sha256": sha256((theorem_type(command) if command.kind in PROOF else command.text).encode("utf-8"))})
        if re.search(r"\b(?:LeanCert|leancert)\b|#assert_trust\b", source_mask(body)):
            raise ValueError(f"Retained declaration uses a forbidden utility symbol in {module}")
        closers = scope_closures(body)
        pieces.append("\nsection\n/- Original module: " + module + " -/\n" + body.rstrip() + "\n" + "".join(x + "\n" for x in closers) + "end\n")
        records.append({"module": module, "original_sha256": sha256(sources[module_key(project, module)]), "declarations": rendered})
    challenge_text = neutralize_doc_comments("\n".join(pieces))
    blank_lines_removed = 0
    if len(challenge_text.splitlines()) > 1000:
        # Empty layout lines carry no Lean tokens. Protect every quoted string
        # span (including conservative matches in comments) before removing them.
        protected_lines = set()
        for string in re.finditer(r'"(?:\\.|[^"\\])*"', challenge_text, re.S):
            first = challenge_text.count("\n", 0, string.start())
            last = challenge_text.count("\n", 0, string.end())
            protected_lines.update(range(first, last + 1))
        raw_lines = challenge_text.splitlines(keepends=True)
        kept = []
        for index, line in enumerate(raw_lines):
            if not line.strip() and index not in protected_lines:
                blank_lines_removed += 1
            else:
                kept.append(line)
        challenge_text = "".join(kept)
    challenge = challenge_text.encode("utf-8")
    lines = len(challenge.splitlines())
    diagnostics = {"schema_version": 1, "id": project, "status": "static-pruned; requires actual Lean elaboration and official comparison", "primary_theorem_names": primary_names, "supporting_theorem_names": supporting_names, "challenge_lines": lines, "challenge_bytes": len(challenge), "selected_commands": len(selected), "nonsemantic_blank_lines_removed": blank_lines_removed, "ambiguous_identifier_resolutions": ambiguities, "unresolved_project_identifiers": unresolved, "source_modules": records}
    write_json(ROOT / "audit" / "extraction-diagnostics" / f"{project}.json", diagnostics)
    if lines > 1000 or len(challenge) > 100 * 1024:
        raise ValueError(f"{project} pruned Challenge still exceeds caps ({lines} lines/{len(challenge)} bytes); inspect diagnostics")
    architecture = load_json(ROOT / "docs" / "build-architecture.json")
    proof_roots = next(x["roots"] for x in architecture["minimum_claim_proof_closure"]["projects"] if x["project"] == project)
    if "Solution" in proof_roots:
        raise ValueError("Existing generic Solution root requires explicit renaming")
    import_roots = solution_import_roots(entry, proof_roots)
    solution = ("module\n" + "".join("public import " + module + "\n" for module in import_roots) + "\n@[expose] public section\n/- All current mapped proof roots are compiled. The compared theorem names, including\nsupporting construction certificates, are original genuinely proved declarations. -/\n").encode("utf-8")
    if project == "TR-04":
        solution = ("module\n" + "".join("public import " + module + "\n" for module in import_roots) +
            "\n@[expose] public section\n/- The selected theorem and its supporting certificates use the original primary\nsolution environment. All inventoried auxiliary proof modules are built independently;\nolder arithmetic implementations deliberately share names and cannot be co-imported. -/\n").encode("utf-8")
    config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": all_names, "definition_names": [], "enable_nanoda": True, "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
    outputs = {f"projects/{project}/Challenge.lean": challenge, f"projects/{project}/Solution.lean": solution, f"projects/{project}/comparator.json": (json.dumps(config, indent=2) + "\n").encode("utf-8")}
    outputs, interface_overrides = apply_interface_overrides(project, outputs)
    challenge = outputs[f"projects/{project}/Challenge.lean"]
    lines = len(challenge.splitlines())
    if lines > 1000 or len(challenge) > 100 * 1024:
        raise ValueError(f"{project} final interface override exceeds Challenge limits")
    previous = load_json(INTERFACES) if INTERFACES.exists() else {"entries": []}
    old = next((x for x in previous["entries"] if x["id"] == project), None)
    old_hashes = {x["path"]: x["sha256"] for x in old["outputs"]} if old else {}
    for name, output in outputs.items():
        target = ROOT / Path(name)
        if target.exists() and target.read_bytes() != output and not force and old_hashes.get(name) != sha256(target.read_bytes()):
            raise ValueError(f"Refusing to overwrite hand-edited entry file: {name}")
    for name, output in outputs.items():
        (ROOT / Path(name)).write_bytes(output)
    result = {"id": project, "status": "generated-static; requires real Lean 4.35 build and official comparison", "mode": "conservative declaration dependency extraction; every theorem placeholder explicitly selected", "primary_theorem_names": primary_names, "supporting_theorem_names": supporting_names, "supporting_theorem_roles": {name: "Well-definedness or construction certificate needed by unchanged semantic definitions and exact theorem types" for name in supporting_names}, "theorem_names": all_names, "challenge_lines": lines, "challenge_bytes": len(challenge), "challenge_direct_imports": ["Mathlib"], "original_external_imports": sorted(external), "applied_interface_overrides": interface_overrides, "solution_proof_roots": proof_roots, "solution_import_roots": import_roots, "independently_built_proof_roots": proof_roots, "diagnostics": f"audit/extraction-diagnostics/{project}.json", "outputs": [{"path": name, "sha256": sha256(output), "bytes": len(output)} for name, output in outputs.items()]}
    previous["schema_version"] = 1
    previous["semantic_extractor_sha256"] = sha256(Path(__file__).read_bytes())
    previous["entries"] = sorted([x for x in previous["entries"] if x["id"] != project] + [result], key=lambda x: x["id"])
    write_json(INTERFACES, previous)
    refresh_entry_inventory(previous["entries"])
    return {key: result[key] for key in ("id", "challenge_lines", "challenge_bytes", "supporting_theorem_names", "status")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ids", nargs="+", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    try:
        sources = read_inputs()
        entries = load_json(PRIMARY)["entries"]
        result = [build(next(x for x in entries if x["id"] == project), sources, args.force) for project in args.ids]
    except (OSError, ValueError, KeyError, StopIteration) as error:
        parser.exit(1, f"Semantic surface extraction failed: {error}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
