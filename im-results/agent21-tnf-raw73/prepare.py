"""Generate the raw73 audit from digest-pinned candidate witnesses."""
from pathlib import Path
import json, shutil, subprocess, sys
root=Path(__file__).resolve().parent
shared=root.parent/"agent10-tnf-multipump"
bank=(root/"dfa-bank.txt").read_text().strip().split(",")
index=(root/"dfa-index.txt").read_text().strip()
assert len(index)==450
words=[index[i:i+2] for i in range(0,len(index),2)]
assert [i for i,w in enumerate(words) if w=="zy"]==[89]
spec={"73":{"bound":7014,"b1":"0LD","hash":"55ba96537acce2e6b0bd2fea4ac9bb6768f7ced7cc30db3756f2857e4a5a54c9","stats":{"cycle":11624,"last":1929,"open":225,"split":598},"root":[9,8],"dfa":" ".join(f"{i}:{bank[int(w,36)]}" for i,w in enumerate(words) if w!="zy"),"one":[89],"two":[]}}
(root/"specs.json").write_text(json.dumps(spec))
for name in ("generate.py","multi.py","long_epoch.py"):
    shutil.copyfile(shared/name,root/("generate-shared.py" if name=="generate.py" else name))
subprocess.run([sys.executable,str(root/"generate-shared.py"),"73"],check=True)
subprocess.run([sys.executable,str(shared/"chunk_checks.py"),str(root),"Raw73","--limit","180"],check=True)
