"""Reuse the generic sibling generator with this independently discovered witness bank."""
from pathlib import Path
import json, subprocess, sys, shutil
root=Path(__file__).resolve().parent
shared=root.parent/"agent10-tnf-multipump"
bank=(root/"dfa-bank.txt").read_text().strip().split(",")
indices=(root/"dfa-index.txt").read_text().strip()
assert len(indices)==1798
words=[indices[2*i:2*i+2] for i in range(899)]
pumps=[i for i,w in enumerate(words) if w=="zz"]
assert pumps==[0,7,83,108,111,724]
spec={"71":{"bound":395,"b1":"1LC","hash":"86b0e251fd07f6212c64700f9e6fb502c50d81a85fa51a5bd12170dfe7210530","stats":{"cycle":36353,"last":8588,"open":899,"split":1992},"root":[8,5],"dfa":" ".join(f"{i}:{bank[int(w,36)]}" for i,w in enumerate(words) if w!="zz"),"one":pumps,"two":[]}}
(root/"specs.json").write_text(json.dumps(spec))
# The generic generator uses __file__ to select its workspace. Copy it and
# its two optional discovery imports so generated modules stay local.
for name in ("generate.py","multi.py","long_epoch.py"):
    shutil.copyfile(shared/name,root/("generate-shared.py" if name=="generate.py" else name))
subprocess.run([sys.executable,str(root/"generate-shared.py"),"71"],check=True)
subprocess.run([sys.executable,str(shared/"chunk_checks.py"),str(root),"Raw71","--limit","180"],check=True)
