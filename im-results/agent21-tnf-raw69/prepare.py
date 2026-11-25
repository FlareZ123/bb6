"""Generate raw69 candidate audit from digest-pinned exact witnesses."""
from pathlib import Path
import json, shutil, subprocess, sys, runpy
root=Path(__file__).resolve().parent
shared=root.parent/"agent10-tnf-multipump"
bank=(root/"dfa-bank.txt").read_text().strip().split(",")
index=(root/"dfa-index.txt").read_text().strip()
assert len(index)==574
words=[index[i:i+2] for i in range(0,len(index),2)]
assert [i for i,w in enumerate(words) if w=="zy"]==[]
spec={"69":{"bound":7014,"b1":"0LC","hash":"dbaa9b7d9fea274f154a6d44468ab52a020d2b876458645b314fd7898d4d2707","stats":{"cycle":14203,"last":1887,"open":287,"split":711},"root":[8,5],"dfa":" ".join(f"{i}:{bank[int(w,36)]}" for i,w in enumerate(words) if w!="zy"),"one":[],"two":[]}}
(root/"specs.json").write_text(json.dumps(spec))
for name in ("generate.py","multi.py","long_epoch.py"):
    shutil.copyfile(shared/name,root/("generate-shared.py" if name=="generate.py" else name))
subprocess.run([sys.executable,str(root/"generate-shared.py"),"69"],check=True)
subprocess.run([sys.executable,str(shared/"chunk_checks.py"),str(root),"Raw69","--limit","180"],check=True)
