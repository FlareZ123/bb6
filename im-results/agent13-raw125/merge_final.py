"""Assemble two successful source-audited closures; reject source conflicts."""
from pathlib import Path
import os
import shutil
import subprocess
import sys

base, target = map(Path, sys.argv[1:])
dirs = [base / "cut", *sorted((base / "residuals").iterdir())]
assert len(dirs) == 5, dirs
target.mkdir(parents=True, exist_ok=False)
checker = Path(__file__).with_name("CompareKernelImports.lean").resolve()
conflicts = set()
for part in dirs:
    sources = sorted(part.rglob("*.lean"))
    assert sources, part
    for source in sources:
        rel = source.relative_to(part)
        assert source.with_suffix(".olean").is_file(), source
        dest = target / rel
        if dest.exists():
            assert dest.read_bytes() == source.read_bytes(), ("source conflict", rel)
            selected = dest.with_suffix(".olean")
            incoming = source.with_suffix(".olean")
            if selected.read_bytes() != incoming.read_bytes():
                subprocess.run(["lean", "--run", str(checker), str(selected.resolve()), str(incoming.resolve())], check=True)
                conflicts.add(rel.stem)
            continue
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        for obj in source.parent.glob(source.stem + ".olean*"):
            shutil.copy2(obj, dest.parent / obj.name)
for name in ["Raw125Cut", *[f"Raw125NGram{i:02}" for i in range(6)], *[f"Raw125Block{i:02}" for i in range(20)]]:
    assert (target / (name + ".olean")).is_file(), name
print("Merged", len(list(target.rglob("*.olean"))), "audited modules")

# Keep the cut's SparseZipper object and re-elaborate the n-gram slice
# against the selected imports, as in the successful local audit.
env = dict(os.environ, LEAN_PATH=str(target.resolve()))
for name in ["NGramCertificate", *[f"Raw125NGram{i:02}" for i in range(6)]]:
    assert (target / (name + ".lean")).is_file(), name
    result = subprocess.run(
        ["lean", "-o", name + ".olean", name + ".lean"],
        cwd=target, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    print(result.stdout, flush=True)
    if result.returncode or "sorryAx" in result.stdout or "native_decide" in result.stdout:
        raise RuntimeError(f"Lean source audit failed: {name}")
print("Rebuilt n-gram dependency slice; kernel-equal shared conflicts:", sorted(conflicts))
