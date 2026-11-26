"""Regenerate the exact Lean certificate source. Run with Python 3."""
import sys, hashlib, json
from pathlib import Path
from collections import Counter
from emit import emit
here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/'agent48-raw139-f1-oneLA'))
sys.path.insert(0,str(here.parent/'agent48-raw139-f1-oneRA'))
from scan import tree, scan
from blockcert import generate

parent=[7,24,11,24,14,0,3,16,12,11,24,24]
counts=Counter(); opens=[]
tr=tree(parent,counts,opens,300,2)
assert counts==dict(maxquery=260,split=85,cycle=1251,last=546,open=48,far=111)
assert opens[9]==[7,21,11,13,14,0,3,16,12,11,5,24]
assert scan(opens[9],3000)==('cycle',2075,10,True,39)
params=[(2,1,2,1,False),(2,1,2,2,False),(2,2,4,2,False),(2,1,2,3,True),(3,1,2,1,False),(3,1,2,2,False),(3,2,4,2,False),(2,1,4,4,True),(2,2,2,3,False),(3,1,2,3,True)]
blocks={}
for i,p in enumerate(opens):
    if i==9: continue
    for width,cap,mod,runs,phase in params:
        c=generate(p,width,cap,mod,runs,False,40000,phase)
        if c:
            blocks[str(i)]=c
            break
    else: raise RuntimeError(f"unresolved leaf {i}")
assert len(blocks)==47
j=dict(parent=parent,counts=dict(counts),tree=tr,open=opens)
out=here/'generated'
emit(j,blocks,out)
lines=''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.name}\n' for p in sorted(out.glob('*.lean')))
digest=hashlib.sha256(lines.encode()).hexdigest()
assert digest=='b579407267b55ad76f2d43e29102e75003127d859e585d1b30c11c04b7b690ea',digest
print(counts, 'source manifest SHA256:',digest)
