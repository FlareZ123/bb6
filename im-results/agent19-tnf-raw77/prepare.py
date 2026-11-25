"""Regenerate the raw77 candidate exhaustive certificate."""
from pathlib import Path
import json, subprocess, sys, shutil
root=Path(__file__).resolve().parent
shared=root.parent/"agent10-tnf-multipump"
bank=(root/"dfa-bank.txt").read_text().strip().split(",")
indices=(root/"dfa-index.txt").read_text().strip()
assert len(indices)==1990
words=[indices[2*i:2*i+2] for i in range(995)]
long_params={"119":["R",4,1],"305":["R",5,1],"316":["R",5,1],"332":["R",4,1],"382":["R",1,1],"552":["L",4,6],"555":["R",1,1],"843":["R",4,1],"858":["R",2,1],"869":["R",4,3],"911":["R",4,3],"923":["R",2,6],"928":["R",1,3]}
long_two={"289":["L",4,2],"352":["R",4,1],"378":["L",1,4]}
late={"89":[1041,11],"349":[1599,11],"637":[1596,11],"787":[1556,1]}
assert set(map(int,long_params))=={i for i,w in enumerate(words) if w=="zw"}
assert set(map(int,long_two))=={i for i,w in enumerate(words) if w=="zv"}
assert set(map(int,late))=={i for i,w in enumerate(words) if w=="zu"}
spec={"77":{"bound":7014,"b1":"0LE","hash":"bd9e4d992f0476dc34f1b037208e0509bfd64d2a9cb1b3303b99f4feccc9b3e5","stats":{"cycle":11169,"last":2396,"open":995,"split":632},"root":[16,8],"dfa":" ".join(f"{i}:{bank[int(w,36)]}" for i,w in enumerate(words) if not w.startswith("z")),"one":[i for i,w in enumerate(words) if w=="zy"],"two":[i for i,w in enumerate(words) if w=="zx"],"long":[i for i,w in enumerate(words) if w=="zw"],"long_params":long_params,"long_two":long_two,"late":late}}
(root/"specs.json").write_text(json.dumps(spec))
for name in ("generate.py","multi.py","long_epoch.py"):
    shutil.copyfile(shared/name,root/("generate-shared.py" if name=="generate.py" else name))
subprocess.run([sys.executable,str(root/"generate-shared.py"),"77"],check=True)
subprocess.run([sys.executable,str(shared/"chunk_checks.py"),str(root),"Raw77","--limit","180"],check=True)
