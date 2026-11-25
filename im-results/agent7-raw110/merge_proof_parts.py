"""Merge successful same-run Lean closures, checking duplicate sources.

Every input artifact comes from a successful source compilation at the same
checkout and toolchain. No proof search or unverified cached module is used.
"""
from pathlib import Path
import shutil
import sys

parent_only = "--parent-only" in sys.argv
parts, target = map(Path, [a for a in sys.argv[1:] if a != "--parent-only"])
target.mkdir(parents=True, exist_ok=False)
dirs = sorted(p for p in parts.iterdir() if p.is_dir())
assert len(dirs) == (7 if parent_only else 8), dirs
for part in dirs:
    sources = sorted(part.rglob("*.lean"))
    assert sources
    for source in sources:
        rel = source.relative_to(part)
        proof = source.with_suffix(".olean")
        assert proof.is_file(), source
        dst = target / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        if dst.exists():
            assert dst.read_bytes() == source.read_bytes(), ("source conflict", rel)
            continue
        shutil.copy2(source, dst)
        for file in source.parent.glob(source.stem + ".olean*"):
            shutil.copy2(file, dst.parent / file.name)
assert (target / ("Raw110Base.olean" if parent_only else "Raw110Consumer.olean")).is_file()
assert len(list(target.glob("Raw110Partial[0-9][0-9].olean"))) == 16
print("Merged", len(list(target.rglob("*.olean"))), "compiled modules")
