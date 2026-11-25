"""Merge the audited raw123 cut and all six residual parts.

The workflow separately checks run/job provenance. Overlap must have
identical Lean source, and every source must have its compiled object.
The final theorem is compiled by Lean against the merged closure.
"""
from pathlib import Path
import shutil
import sys

base,target=map(Path,sys.argv[1:])
expected={f"raw123-residual-{i}" for i in range(6)}
actual={p.name for p in (base/"residuals").iterdir() if p.is_dir()}
assert actual==expected,(actual,expected)
dirs=[base/"cut",*sorted((base/"residuals").iterdir())]
target.mkdir(parents=True,exist_ok=False)
for part in dirs:
    sources=sorted(part.rglob("*.lean"))
    assert sources,part
    for source in sources:
        rel=source.relative_to(part)
        obj=source.with_suffix(".olean")
        assert obj.is_file(),source
        dest=target/rel
        if dest.exists():
            assert dest.read_bytes()==source.read_bytes(),("source conflict",rel)
            continue
        dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(source,dest)
        for obj in source.parent.glob(source.stem+".olean*"):
            shutil.copy2(obj,dest.parent/obj.name)
for name in ["Raw123Cut",*[f"Raw123NGram{i:02}" for i in range(19)],*[f"Raw123Block{i:02}" for i in range(21)]]:
    assert (target/(name+".olean")).is_file(),name
print("Merged",len(list(target.rglob("*.olean"))),"audited modules")
