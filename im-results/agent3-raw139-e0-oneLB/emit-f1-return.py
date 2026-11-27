#!/usr/bin/env python3
"""Generate candidate F1 macro edges; original-source Lean proves them."""
from pathlib import Path
import sys
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
def pack(w): return int(w[::-1] or "0",2)
def step(u):
    u=u.rstrip("0")+"0"*8; assert u[0]=="1"
    i=1; runs=[]; phi=[]
    while True:
        if u[i]=="1": t="b";i+=1
        elif u[i:i+2]=="00": d=0;i+=2;break
        elif u[i:i+3]=="010": t="a";i+=3
        elif u[i:i+5]=="01100":t="a1";i+=5
        elif u[i:i+6]=="011011":d=1;i+=6;break
        else: raise ValueError(("unknown token",u[i:i+20]))
        if runs and runs[-1][0]==t:runs[-1][1]+=1
        else:runs.append([t,1])
        phi.append({"a":"100","a1":"10101","b":"0"}[t])
    a=sum(n for t,n in runs if t=="a")
    a1=sum(n for t,n in runs if t=="a1")
    b=sum(n for t,n in runs if t=="b")
    tail=u[i:].rstrip("0")
    if d:return runs,d,pack(tail),None,9+11*a+13*a1+3*b
    v=("10"+"".join(phi)+"101"+tail).rstrip("0")
    return runs,d,pack(tail),v,12+16*a+30*a1+4*b
def rle(rs):return "["+",".join(f"(.{t},{n})" for t,n in rs)+"]"
hdr="""set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3OneLBF1Return
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay
"""
u="11";start=pack(u);records=[];chunk=[];cs=0;total=0
for k in range(10000):
    rs,d,t,v,c=step(u)
    if d:
        stop=rs,t,c;break
    chunk.append(f"⟨{rle(rs)},{hex(t)}⟩");u=v;cs+=c
    if len(chunk)==64 or k==2727:
        i=len(records);end=pack(u);name=f"OneLBF1ReturnChunk{i:03}"
        lines=["import F1ReturnRLE",hdr,f"def rows{i} : List Row := [",",\n".join(chunk),"]"]
        lines.append(f"theorem chunk{i} : runP (parent false) {cs} (frontNum {hex(start)}) = some (frontNum {hex(end)}) :=\n  replay_sound false rows{i} {hex(start)} {cs} {hex(end)} (by decide +kernel)")
        (out/(name+".lean")).write_text("\n".join(lines)+"\nend BB6.Agent3OneLBF1Return\n")
        records.append((name,start,end,cs));total+=cs
        chunk=[];cs=0;start=end
else:raise RuntimeError("no terminal")
assert k==2728 and not chunk
rs,t,c=stop
assert 2+total+c==31790091
assert all(records[i][2]==records[i+1][1] for i in range(len(records)-1))
lines=[*(f"import {r[0]}" for r in records),hdr,f"def finalRuns : RLE := {rle(rs)}"]
def combine(lo,hi):
    if hi-lo==1:return f"chunk{lo}",records[lo][3]
    mid=(lo+hi)//2
    a,n=combine(lo,mid);b,m=combine(mid,hi);name=f"joined{lo}_{hi}"
    lines.append(f"theorem {name} : runP (parent false) {n+m} (frontNum {hex(records[lo][1])}) = some (frontNum {hex(records[hi-1][2])}) :=\n  joinP {a} {b}")
    return name,n+m
joined,n=combine(0,len(records));N=2+n+c
lines.append(f"""theorem readFinal : readRunP (parent false) {N} = some (5,true) := by
  have hb : runP (parent false) 2 startP = some (frontNum 3) := packed_entry false
  have hs : stopBefore finalRuns {hex(t)} = {hex(start)} := by decide +kernel
  have hc : stopCost false finalRuns = {c} := by decide +kernel
  obtain ⟨p,hp,hr⟩ := stop_sound false finalRuns {hex(t)}
  rw [hs,hc] at hp
  have h : runP (parent false) {N} startP = some p := joinP (joinP hb {joined}) hp
  simp only [readRunP,h,Option.map_some,hr]
def B : Nat := 187672026
theorem root : parent false initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt (parent false) := by
  intro s
  unfold parent fromCodes
  cases h : (codes false)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h,hn]
theorem checked : packedCheck B (parent false) (.last {N} (5,true)) = true := by
  simp only [packedCheck,packedQueryOK,readFinal]
  decide +kernel
theorem weighted : ∀ m, compatible (parent false) m → WeightedBound B m :=
  (certifiedPacked B (parent false) _ root nohalt checked).sound
#print axioms readFinal
#print axioms weighted
end BB6.Agent3OneLBF1Return
""")
(out/"OneLBF1ReturnFinal.lean").write_text("\n".join(lines))
print("generated",len(records),"chunks; return steps",total,"terminal",c)
