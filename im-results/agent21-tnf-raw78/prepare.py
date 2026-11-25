"""Generate raw78 candidate audit from digest-pinned exact witnesses."""
from pathlib import Path
import json, shutil, subprocess, sys, runpy
root=Path(__file__).resolve().parent
shared=root.parent/"agent10-tnf-multipump"
bank=(root/"dfa-bank.txt").read_text().strip().split(",")
index=(root/"dfa-index.txt").read_text().strip()
assert len(index)==806
words=[index[i:i+2] for i in range(0,len(index),2)]
assert [i for i,w in enumerate(words) if w=="zy"]==[156]
spec={"78":{"bound":7014,"b1":"0RE","hash":"68c4a7b369fa24e63e8a119a27470c75746d4f0f489ca35d9faeddac75364890","stats":{"cycle":16423,"last":2955,"open":403,"split":859},"root":[8,8],"dfa":" ".join(f"{i}:{bank[int(w,36)]}" for i,w in enumerate(words) if w!="zy"),"one":[156],"two":[]}}
(root/"specs.json").write_text(json.dumps(spec))
for name in ("generate.py","multi.py","long_epoch.py"):
    shutil.copyfile(shared/name,root/("generate-shared.py" if name=="generate.py" else name))
# Known long epoch: avoid re-discovering the insertion cut by broad search.
sys.path.insert(0,str(root.parent/"agent31-three-hole-tnf"))
sys.path.insert(0,str(root))
import generate_sweeps as one
def exact_candidate(p,events):
    assert one.show(p)=="1RB1LB_1RC0RE_0RD1RA_1LD1RE_1LF0LB_0LA---"
    t,c=next((t,c) for t,s,c in events if t==111 and s=="L" and c.q==0)
    assert c.r.pre=="0"+"1"*10 and c.l.pre==""
    start=one.C(0,0,0,one.W(),one.W(c.r.pre,"1"*12,""))
    target=one.C(0,-3,0,one.W(),one.W(c.r.pre+"1"*12,"1"*12,""))
    ans=one.pump(p,start,target,500)
    assert ans is not None
    assert sum(x[3] for x in ans[0] if x[0]=="step")==473
    assert sum(x[3] for x in ans[0] if x[0]=="loop")==372
    return t,c,start,target,ans
one.candidate=exact_candidate
sys.argv=[str(root/"generate-shared.py"),"78"]
runpy.run_path(sys.argv[0],run_name="__main__")
subprocess.run([sys.executable,str(shared/"chunk_checks.py"),str(root),"Raw78","--limit","180"],check=True)
