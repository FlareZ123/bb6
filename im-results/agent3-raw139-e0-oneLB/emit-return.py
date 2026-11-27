#!/usr/bin/env python3
"""Untrusted generator: Lean checks every compressed edge and both clocks."""
from pathlib import Path
import sys
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
def pack(w): return int(w[::-1] or "0",2)
def step(u):
    u=u.rstrip("0")+"0"*8
    assert u[0]=="1"
    i=1; runs=[]; phi=[]
    while True:
        if u[i]=="1": t="b";i+=1
        elif u[i+1]=="0": d=0;i+=2;break
        elif u[i+2]=="0": t="a";i+=3
        elif u[i+3]=="0": d=1;i+=4;break
        else: d=2;i+=4;break
        if runs and runs[-1][0]==t: runs[-1][1]+=1
        else: runs.append([t,1])
        phi.append("100" if t=="a" else "0")
    a=sum(n for t,n in runs if t=="a")
    b=sum(n for t,n in runs if t=="b")
    tail=u[i:].rstrip("0")
    if d==2: return runs,d,pack(tail),None,(5+3*a+3*b,5+7*a+3*b)
    v=("10"+"".join(phi)+("10011" if d else "101")+tail).rstrip("0")
    return runs,d,pack(tail),v,(12+8*a+4*b+4*d,12+12*a+4*b+4*d)
def rle(rs):return "["+",".join(f"(.{t},{n})" for t,n in rs)+"]"
def row(rs,d,w):return f"⟨{rle(rs)},{str(bool(d)).lower()},{hex(w)}⟩"
hdr="""set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3OneLBReturn
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay
"""
u="11";start=pack(u);records=[];chunk=[];cs=[0,0];total=[0,0]
for k in range(10000):
    rs,d,t,v,c=step(u)
    if d==2:
        stop=rs,t,c;break
    chunk.append(row(rs,d,t));u=v
    cs=[cs[j]+c[j] for j in range(2)]
    if len(chunk)==64 or k==7655:
        i=len(records);end=pack(u);name=f"OneLBReturnChunk{i:03}"
        lines=["import ReturnRLE",hdr,f"def rows{i} : List Row := [",",\n".join(chunk),"]"]
        for j,slow in enumerate(("false","true")):
            lines.append(f"theorem chunk{i}_{j} : runP (parent {slow}) {cs[j]} (frontNum {hex(start)}) = some (frontNum {hex(end)}) :=\n  replay_sound {slow} rows{i} {hex(start)} {cs[j]} {hex(end)} (by decide +kernel)")
        (out/(name+".lean")).write_text("\n".join(lines)+"\nend BB6.Agent3OneLBReturn\n")
        records.append((name,start,end,tuple(cs)))
        total=[total[j]+cs[j] for j in range(2)]
        chunk=[];cs=[0,0];start=end
else:raise RuntimeError("no terminal")
assert k==7656 and not chunk
rs,t,c=stop
assert [2+total[j]+c[j] for j in range(2)]==[125150404,187672020]
assert all(records[i][2]==records[i+1][1] for i in range(len(records)-1))
lines=[*(f"import {r[0]}" for r in records),hdr,f"def finalRuns : RLE := {rle(rs)}"]
def combine(j,lo,hi):
    if hi-lo==1:return f"chunk{lo}_{j}",records[lo][3][j]
    mid=(lo+hi)//2
    a,n=combine(j,lo,mid);b,m=combine(j,mid,hi)
    name=f"joined{j}_{lo}_{hi}"
    slow=str(bool(j)).lower()
    lines.append(f"theorem {name} : runP (parent {slow}) {n+m} (frontNum {hex(records[lo][1])}) = some (frontNum {hex(records[hi-1][2])}) :=\n  joinP {a} {b}")
    return name,n+m
for j,slow in enumerate(("false","true")):
    joined,n=combine(j,0,len(records))
    N=2+n+c[j]
    lines.append(f"""theorem readFinal{j} : readRunP (parent {slow}) {N} = some (0,true) := by
  have hb : runP (parent {slow}) 2 startP = some (frontNum 3) := packed_entry {slow}
  have hs : stopBefore finalRuns {hex(t)} = {hex(start)} := by decide +kernel
  have hc : stopCost {slow} finalRuns = {c[j]} := by decide +kernel
  obtain ⟨p,hp,hr⟩ := stop_sound {slow} finalRuns {hex(t)}
  rw [hs,hc] at hp
  have h : runP (parent {slow}) {N} startP = some p := joinP (joinP hb {joined}) hp
  simp only [readRunP,h,Option.map_some,hr]
""")
lines.append("""def B : Nat := 187672026
theorem root (slow : Bool) : parent slow initialSlot = some (some ⟨true,true,1⟩) := by
  cases slow <;> decide +kernel
theorem nohalt (slow : Bool) : weightedTNFNoAssignedHalt (parent slow) := by
  intro s
  unfold parent fromCodes
  cases h : (codes slow)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h,hn]
theorem checked0 : packedCheck B (parent false) (.last 125150404 (0,true)) = true := by
  simp only [packedCheck,packedQueryOK,readFinal0]
  decide +kernel
theorem checked1 : packedCheck B (parent true) (.last 187672020 (0,true)) = true := by
  simp only [packedCheck,packedQueryOK,readFinal1]
  decide +kernel
theorem weighted0 : ∀ m, compatible (parent false) m → WeightedBound B m :=
  (certifiedPacked B (parent false) _ (root false) (nohalt false) checked0).sound
theorem weighted1 : ∀ m, compatible (parent true) m → WeightedBound B m :=
  (certifiedPacked B (parent true) _ (root true) (nohalt true) checked1).sound
theorem both_weighted :
    (∀ m, compatible (parent false) m → WeightedBound B m) ∧
    (∀ m, compatible (parent true) m → WeightedBound B m) :=
  ⟨weighted0,weighted1⟩
#print axioms readFinal0
#print axioms readFinal1
#print axioms both_weighted
end BB6.Agent3OneLBReturn
""")
(out/"OneLBReturnFinal.lean").write_text("\n".join(lines))
print("generated",len(records),"chunks; return steps",total,"terminal",c)
