"""Assemble two successful source-audited closures; reject source conflicts."""
from pathlib import Path
import shutil
import sys

base, target = map(Path, sys.argv[1:])
dirs = [base / "cut", *sorted((base / "residuals").iterdir())]
assert len(dirs) == 5, dirs
target.mkdir(parents=True, exist_ok=False)
for part in dirs:
    sources = sorted(part.rglob("*.lean"))
    assert sources, part
    for source in sources:
        rel = source.relative_to(part)
        assert source.with_suffix(".olean").is_file(), source
        dest = target / rel
        if dest.exists():
            assert dest.read_bytes() == source.read_bytes(), ("source conflict", rel)
            continue
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        for obj in source.parent.glob(source.stem + ".olean*"):
            shutil.copy2(obj, dest.parent / obj.name)
for name in ["Raw125Cut", *[f"Raw125NGram{i:02}" for i in range(6)], *[f"Raw125Block{i:02}" for i in range(20)]]:
    assert (target / (name + ".olean")).is_file(), name
print("Merged", len(list(target.rglob("*.olean"))), "audited modules")
