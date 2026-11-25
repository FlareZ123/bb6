"""Regenerate the raw81 candidate exhaustive certificate."""
from pathlib import Path
import json, subprocess, sys, shutil
root=Path(__file__).resolve().parent
shared=root.parent/"agent10-tnf-multipump"
bank=(root/"dfa-bank.txt").read_text().strip().split(",")
indices=(root/"dfa-index.txt").read_text().strip()
assert len(indices)==3586
words=[indices[2*i:2*i+2] for i in range(1793)]
long_params={"37":["R",1,1],"38":["R",5,1],"140":["L",1,5],"825":["R",1,1],"1753":["R",2,1]}
late={"1161":[1325,8]}
late_cycle={"1543":[0,266,False,11]}
assert set(map(int,long_params))=={i for i,w in enumerate(words) if w=="zw"}
assert set(map(int,late))=={i for i,w in enumerate(words) if w=="zu"}
assert set(map(int,late_cycle))=={i for i,w in enumerate(words) if w=="zt"}
special={"zy","zx","zw","zu","zt"}
spec={"81":{"bound":7014,"b1":"0LF","hash":"fc0a5d18ab105646556158b9cbe6f867982ad39681fc5a80e49a14b62849f726","stats":{"cycle":40778,"last":8628,"open":1793,"split":2225},"root":[8,11],"dfa":" ".join(f"{i}:{bank[int(w,36)]}" for i,w in enumerate(words) if w not in special),"one":[i for i,w in enumerate(words) if w=="zy"],"two":[i for i,w in enumerate(words) if w=="zx"],"long":[i for i,w in enumerate(words) if w=="zw"],"long_params":long_params,"late":late,"late_cycle":late_cycle}}
(root/"specs.json").write_text(json.dumps(spec))
for name in ("generate.py","multi.py","long_epoch.py"):
    shutil.copyfile(shared/name,root/("generate-shared.py" if name=="generate.py" else name))
subprocess.run([sys.executable,str(root/"generate-shared.py"),"81"],check=True)
subprocess.run([sys.executable,str(shared/"chunk_checks.py"),str(root),"Raw81","--limit","180"],check=True)
