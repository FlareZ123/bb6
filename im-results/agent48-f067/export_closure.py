"""Pack the exact compiled imports of Basic/Bridge for local Lean, without core libraries."""
import os, pathlib, shutil, subprocess, sys, tarfile, tempfile
from pathlib import Path

names = {line.split()[1] for line in Path(sys.argv[1]).read_text().splitlines()}
names.update(("BusyBeaver.Basic", "BusyBeaver.Bridge"))
prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
roots = [Path(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
with tempfile.TemporaryDirectory() as td:
    dest = Path(td)
    for name in sorted(names):
        rel = Path(*name.split(".")).with_suffix(".olean")
        if (prefix / "lib/lean" / rel).is_file():
            continue
        found = next((p / rel for p in roots if (p / rel).is_file()), None)
        if found is None:
            raise RuntimeError(f"Missing {name}: {roots}")
        target = dest / "lib" / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        for file in found.parent.glob(found.stem + ".*"):
            if file.suffix in (".olean", ".private", ".server", ".ilean", ".ir", ".sig"):
                shutil.copy2(file, target.parent / file.name)
    src = Path(*sys.argv[2].split(".")).with_suffix(".lean")
    target = dest / "source" / src
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, target)
    for folder in ("BusyBeaver",):
        for file in Path(folder).glob("*.lean"):
            target = dest / "source" / file
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(file, target)
    (dest / "revision.txt").write_text(subprocess.check_output(["git", "rev-parse", "HEAD"], text=True))
    subprocess.run(["tar","--zstd","-cf","/tmp/lean-local-source-closure.tar.zst","-C",td,"."],check=True)
print("Archive bytes:",Path("/tmp/lean-local-source-closure.tar.zst").stat().st_size)
