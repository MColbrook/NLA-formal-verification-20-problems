"""Create a reproducible clean source ZIP for manual upload; never push Git."""
from __future__ import annotations
import argparse, hashlib, json, os, tempfile, zipfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
GENERATED = {".git", ".lake", "__pycache__", ".build-cache"}

def is_link(path: Path) -> bool:
    return path.is_symlink() or getattr(path, "is_junction", lambda: False)()

def create_archive(root: Path, output: Path) -> dict:
    root = root.resolve()
    output = output.absolute()
    if any(is_link(part) for part in (output, *output.parents)):
        raise ValueError("Refusing an output path containing a symlink")
    output = output.resolve()
    if output.is_relative_to(root) and not output.is_relative_to(root / "dist"):
        raise ValueError("An upload ZIP inside the source folder must be under dist/.")
    files = []
    for directory, directories, names in os.walk(root, followlinks=False):
        relative = Path(directory).relative_to(root)
        retained = []
        for name in sorted(directories):
            path = Path(directory) / name
            if name in GENERATED or (relative == Path(".") and name == "dist") or (
                relative == Path("verification") and name == "local-builds"
            ):
                continue
            if is_link(path):
                raise ValueError("Refusing symlink: " + path.relative_to(root).as_posix())
            retained.append(name)
        directories[:] = retained
        for name in sorted(names):
            path = Path(directory) / name
            relative_file = path.relative_to(root).as_posix()
            if is_link(path):
                raise ValueError("Refusing symlink: " + relative_file)
            if name == ".git" or path.suffix == ".pyc":
                continue
            size = path.stat().st_size
            if size >= 100 * 1024 * 1024:
                raise ValueError("A file exceeds GitHub's ordinary file cap: " + relative_file)
            files.append((path, relative_file, size))
    files.sort(key=lambda item: item[1])
    total = sum(size for _, _, size in files)
    if total > 500 * 1024 * 1024:
        raise ValueError("Checkout size exceeds Palomar's cap")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(prefix=".palomar-upload-", suffix=".tmp", dir=output.parent, delete=False) as stream:
            temporary = Path(stream.name)
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for path, relative_file, _ in files:
                info = zipfile.ZipInfo(relative_file, date_time=(1980, 1, 1, 0, 0, 0))
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
        os.replace(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return dict(zip=str(output), sha256=hashlib.sha256(output.read_bytes()).hexdigest(),
                files=len(files), uncompressed_bytes=total, zip_bytes=output.stat().st_size,
                github_upload_performed=False, palomar_submission_performed=False)

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "dist/palomar_submission-upload.zip")
    args = parser.parse_args()
    try:
        result = create_archive(ROOT, args.output)
    except (OSError, ValueError) as error:
        parser.exit(1, str(error) + "\n")
    print(json.dumps(result))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
