#!/usr/bin/env python3
"""Discover compressed replay using the fixed arbitrary-tail sweep catalog."""
from pathlib import Path
import json,sys
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
data=json.loads(Path(__file__).with_name("D0-motifs.json").read_text())
table=data["table"];N=data["steps"]
def pack(w): return sum(x<<i for i,x in enumerate(w))
def word(w):return "["+",".join("true" if x else "false" for x in w)+"]"
def boolean(b):return "true" if b else "false"
def num(z):return f"⟨{z[0]},{hex(z[1])},{hex(z[2])}⟩"
def prim(q,l,r):
    v=table[2*q+(l&1)]
    assert v!=24
    w=(v>>1)&1
    if v&1:return v>>2,(r&1)+2*w+4*(l>>1),r>>1
    return v>>2,l>>1,w+2*r
header="""set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3OneLBD0
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay
"""
motifs=data["motifs"];rules=[]
lines=["import D0Sweep",header]
for i,m in enumerate(motifs):
    for k in ("u","v","x","y"):
        m["p"+k]=pack(m[k]);m[k.upper()]=1<<len(m[k])
    lines.append(f"def rule{i} : Macro := ⟨{m['q']},{boolean(m['left'])},{m['period']},{word(m['u'])},{word(m['v'])},{word(m['x'])},{word(m['y'])}⟩")
    lines.append(f"theorem rule{i}_sound : Valid rule{i} := by intro a b; rfl")
    rules.append(f"⟨rule{i},rule{i}_sound⟩")
lines.append("def rules : Array Rule := #["+",".join(rules)+"]")
(out/"D0Rules.lean").write_text("\n".join(lines)+"\nend BB6.Agent3OneLBD0\n")
def find(q,l,r):
    best=None
    for i,m in enumerate(motifs):
        if q!=m["q"] or l%m["U"]!=m["pu"] or r%m["V"]!=m["pv"]:continue
        x=l//m["U"] if m["left"] else r//m["V"]
        n=0
        while x%m["X"]==m["px"] and n<200:x//=m["X"];n+=1
        if n>=2 and (best is None or m["period"]*(n-1)>best[1]["period"]*(best[2]-1)):
            best=i,m,n,x
    return best
z=(0,0,0);start=z;steps=0;cs=0;rows=[];records=[];mc=pc=0;pending=0
def flush():
    global start,cs,rows,pending
    if pending:rows.append(f".prim {pending}");pending=0
    i=len(records);name=f"D0Chunk{i:03}"
    lines=["import D0Rules",header,f"def rows{i} : List Cmd := [",",\n".join(rows),"]"]
    lines.append(f"theorem chunk{i} : runP (parent false) {cs} {num(start)} = some {num(z)} :=\n  replay_sound rules rows{i} {num(start)} {cs} {num(z)} (by decide +kernel)")
    (out/(name+".lean")).write_text("\n".join(lines)+"\nend BB6.Agent3OneLBD0\n")
    records.append((name,start,z,cs));start=z;cs=0;rows=[]
while steps<N:
    q,l,r=z;best=find(q,l,r)
    if best:
        i,m,n,x=best
        if pending:rows.append(f".prim {pending}");pending=0
        y=r//m["V"] if m["left"] else l//m["U"]
        a,b=(x,y) if m["left"] else (y,x)
        rows.append(f".sweep {i} {n} {hex(a)} {hex(b)}")
        for _ in range(n):y=m["py"]+m["Y"]*y
        if m["left"]:z=q,m["pu"]+m["U"]*x,m["pv"]+m["V"]*y
        else:z=q,m["pu"]+m["U"]*y,m["pv"]+m["V"]*x
        k=m["period"]*n;mc+=1
    else:
        z=prim(q,l,r);k=1;pc+=1;pending+=1
    steps+=k;cs+=k
    if len(rows)>=64:flush()
if rows or pending:flush()
assert steps==N and 2*z[0]+(z[1]&1)==data["slot"]
assert mc==data["macro"] and pc==data["primitive"]
lines=[*(f"import {r[0]}" for r in records),header]
def combine(lo,hi):
    if hi-lo==1:return f"chunk{lo}",records[lo][3]
    mid=(lo+hi)//2;a,n=combine(lo,mid);b,m=combine(mid,hi)
    name=f"joined{lo}_{hi}"
    lines.append(f"theorem {name} : runP (parent false) {n+m} {num(records[lo][1])} = some {num(records[hi-1][2])} :=\n  joinP {a} {b}")
    return name,n+m
joined,n=combine(0,len(records))
assert n==N
lines.append(f"""theorem readFinal : readRunP (parent false) {N} = some (3,false) := by
  have h : runP (parent false) {N} startP = some {num(z)} := {joined}
  simp only [readRunP,h,Option.map_some]
  rfl
def B : Nat := 3643345
theorem root : parent false initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt (parent false) := by
  intro s
  unfold parent fromCodes
  cases h : (codes false)[2*s.1.val+s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h,hn]
theorem checked : packedCheck B (parent false) (.last {N} (3,false)) = true := by
  simp only [packedCheck,packedQueryOK,readFinal]
  decide +kernel
theorem weighted : ∀ m, compatible (parent false) m → WeightedBound B m :=
  (certifiedPacked B (parent false) _ root nohalt checked).sound
#print axioms readFinal
#print axioms weighted
end BB6.Agent3OneLBD0
""")
(out/"D0Final.lean").write_text("\n".join(lines))
print("exact replay candidate",N,"steps",mc,"macro commands",pc,"primitive steps",len(records),"chunks")
