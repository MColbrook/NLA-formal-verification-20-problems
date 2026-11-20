"""Serial development builds with the pinned native Lean compiler.

This does not replace Comparator, fixed-definition checking, the strict Linux
sandbox, or the whole-paper audit. It avoids Lake launching parallel compiler
processes on machines with insufficient memory. Existing public dependency
oleans may be reused; every selected project's local dependency is rebuilt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE))
from lean_source import lean_code_mask


def module_imports(text):
    """Read current Lean import headers, including public/meta/import-all."""
    names=[]
    pending=False
    module_re=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
    for line in lean_code_mask(text).splitlines():
        stripped=line.strip()
        if not stripped or stripped in {'module','prelude'}: continue
        match=re.match(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.*)$",stripped)
        if match:
            parts=match[1].split();pending=True
        elif pending and line[:1].isspace() and all(module_re.fullmatch(p) for p in stripped.split()) and stripped.split()[0] not in {'open','namespace','section','end','variable','universe','set_option','attribute','noncomputable','public','private','def','theorem','instance'}:
            parts=stripped.split()
        else: break
        for name in parts:
            if not module_re.fullmatch(name): raise ValueError('Unsupported import identifier: '+name)
            if name not in names: names.append(name)
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("module", nargs="*")
    parser.add_argument("--all-local", action="store_true", help="Compile every local source independently, including alternative proof environments")
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--resume", action="store_true", help="Reuse only matching development build receipts")
    args = parser.parse_args()
    project = args.project.resolve()
    modules=list(args.module)
    if args.all_local:
        for directory,dirs,files in os.walk(project,followlinks=False):
            dirs[:]=sorted(d for d in dirs if d not in {".git",".lake","__pycache__",".build-cache"})
            for name in sorted(files):
                if name.endswith(".lean"):
                    relative=(Path(directory)/name).relative_to(project).with_suffix("")
                    modules.append(".".join(relative.parts))
    modules=list(dict.fromkeys(modules))
    if not modules: parser.error("Name a module or select --all-local")
    packages = project / ".lake" / "packages"
    roots = [project] + sorted(p for p in packages.iterdir() if p.is_dir())
    build = lambda root: root / ".lake" / "build" / "lib" / "lean"
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(str(build(root)) for root in roots)
    env["LEAN_NUM_THREADS"] = "1"
    done, active, records, signatures = set(), set(), [], {}
    compiler_sha = hashlib.sha256(args.lean.read_bytes()).hexdigest()
    args.log.parent.mkdir(parents=True, exist_ok=True)
    receipt = args.log.with_suffix(".json")
    with args.log.open("w", encoding="utf-8", buffering=1) as log:
        def emit(message):
            print(message, flush=True)
            print(message, file=log, flush=True)

        def compile_module(module):
            if module in done:
                return signatures[module]
            relative = Path(*module.split("."))
            matches = [(root, root / relative.with_suffix(".lean")) for root in roots
                       if (root / relative.with_suffix(".lean")).is_file()]
            if not matches:
                # Init/Lean/Std live in the pinned compiler's own search path.
                if module.split(".")[0] in {"Init", "Lean", "Std", "Lake"}:
                    done.add(module)
                    signatures[module] = compiler_sha
                    return compiler_sha
                raise RuntimeError(f"No source found for imported module {module}")
            if len(matches) != 1:
                raise RuntimeError(f"Ambiguous source for {module}: {matches}")
            root, source = matches[0]
            output = build(root) / relative.with_suffix(".olean")
            if root != project and output.is_file():
                done.add(module)
                signatures[module] = hashlib.sha256(output.read_bytes()).hexdigest()
                return signatures[module]
            if module in active:
                raise RuntimeError(f"Import cycle at {module}")
            active.add(module)
            source_bytes = source.read_bytes()
            imports = {imported: compile_module(imported) for imported in
                       module_imports(source_bytes.decode("utf-8-sig"))}
            binding = dict(source_sha256=hashlib.sha256(source_bytes).hexdigest(),
                           compiler_sha256=compiler_sha, imports=imports)
            signature = hashlib.sha256(json.dumps(binding,sort_keys=True).encode()).hexdigest()
            stamp = output.with_suffix(".native-source.json")
            artifacts = [output, output.with_suffix('.olean.private'), output.with_suffix('.olean.server'),
                         output.with_suffix('.ir'), output.with_suffix('.ir.sig')]
            artifact_hashes = lambda: {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                                      for f in artifacts if f.is_file()}
            if args.resume and all(f.is_file() for f in artifacts) and stamp.is_file():
                prior = json.loads(stamp.read_text(encoding="utf-8"))
                if (prior.get("signature") == signature and
                    prior.get("artifact_sha256") == artifact_hashes()):
                    emit(f"REUSE {module} (matching development receipt)")
                    signatures[module] = signature
                    active.remove(module)
                    done.add(module)
                    return signature
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [str(args.lean.resolve()), "-j1", f"-M{args.memory_mb}",
                       "-o", str(output), str(source)]
            emit(f"BUILD {module} ({root.name})")
            started = time.time()
            completed = subprocess.run(command, cwd=root, env=env, stdout=log,
                                       stderr=subprocess.STDOUT)
            record = dict(module=module, source=str(source), source_sha256=hashlib.sha256(source_bytes).hexdigest(),
                          command=command, exit_code=completed.returncode,
                          seconds=round(time.time()-started, 3))
            records.append(record)
            receipt.write_text(json.dumps(dict(kind="standard-serial-lean-build", fresh_comparator_replay=False,
                lean=str(args.lean.resolve()), project=str(project), modules=modules, all_project_modules_requested=args.all_local,
                records=records), indent=2)+"\n", encoding="utf-8")
            if completed.returncode:
                emit(f"FAIL {module}; see {args.log}")
                raise subprocess.CalledProcessError(completed.returncode, command)
            if not all(f.is_file() for f in artifacts):
                raise RuntimeError("Compiler did not emit the full module artifact set: " + module)
            stamp.write_text(json.dumps(dict(signature=signature,binding=binding,
                artifact_sha256=artifact_hashes()),indent=2)+"\n",encoding="utf-8")
            emit(f"PASS {module} ({record['seconds']}s)")
            active.remove(module)
            done.add(module)
            signatures[module] = signature
            return signature

        for module in modules:
            compile_module(module)
        emit("PASS: serial development build; no Comparator or independent-kernel replay performed.")


if __name__ == "__main__":
    main()
