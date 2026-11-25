"""Merge the late-proof objects into the accepted raw110 parent workspace.

Both inputs were compiled with Lean 4.36.0-rc2. Common module names must
have identical sources at the pinned late checkout and the older child
artifact. A mismatch is a hard error, not an overwrite.
"""
from pathlib import Path
import shutil, sys
parent, late, source = map(Path, sys.argv[1:])
index = {}
for p in source.rglob("*.lean"):
    index.setdefault(p.stem, []).append(p)
for p in sorted(late.glob("*.olean")):
    target = parent / p.name
    if target.exists():
        old = target.with_suffix(".lean")
        assert old.is_file(), ("missing parent source", old)
        candidates = index.get(p.stem, [])
        assert any(c.read_bytes() == old.read_bytes() for c in candidates), (
            "shared source mismatch", p.stem, candidates)
    else:
        shutil.copy2(p, target)
assert (parent / "Raw110LateCover.olean").is_file()
assert (parent / "Raw110ParentResidualMatch.olean").is_file()
print("Merged late proof objects with exact common-source matches.")
