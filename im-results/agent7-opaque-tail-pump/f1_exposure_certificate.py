#!/usr/bin/env python3
"""Produce source-level Lean 4.36 proofs of exact D100 F1 4672258-step first-hole.
Every emitted finite trace step is checked by Lean rfl, never native_decide.
Untrusted producer, not a mathematical result until source-accepted.
"""
from pathlib import Path
import argparse,hashlib,json

TABLE="1RB1LA_1RC1LE_0RD1RE_0LD0LA_1RF0LB_1LD---"
N=4672258
M=[TABLE.replace("_","")[3*i:3*i+3] for i in range(12)]
NS="BB6.Agent7D100F1Exposure"
ORIGIN,SIZE=20000,40000
assert M[11]=="---"

def bits(b):return "["+",".join("true" if c=="1" else "false" for c in b)+"]"
def expr(z):
    q,l,r=z
    return f"⟨{q},{bits(l)},{bits(r)}⟩"

def scan(chunk):
    tape=bytearray(SIZE);h=ORIGIN;q=0;ln=rn=0;snaps=[(0,(0,"",""))]
    for t in range(1,N+1):
        v=tape[h];mv=M[2*q+v]
        if mv=="---":raise ValueError(f"unexpected early hole {t-1}")
        tape[h]=int(mv[0])
        if mv[1]=="R":
            h+=1;ln=max(0,ln-1)+2;rn=max(0,rn-1)
        else:
            h-=1;ln=max(0,ln-1);rn+=1
        if h<=ln or h+rn>=SIZE:raise ValueError(f"tape exceeded sentinel {t}")
        q=ord(mv[2])-65
        if t%chunk==0 or t==N:
            left="".join("1" if tape[h-i] else "0" for i in range(ln))
            right="".join("1" if tape[h+i+1] else "0" for i in range(rn))
            snaps.append((t,(q,left,right)))
    assert q==5 and tape[h]==1 and M[2*q+1]=="---",(q,tape[h])
    assert ln==2334 and rn==21,(ln,rn)
    return snaps,{"steps":N,"last_slot":"F1","last_head":h-ORIGIN,"last_lengths":[ln,rn]}

def header(imports):
    return [*(f"import {x}" for x in imports),
       "set_option maxRecDepth 100000","set_option maxHeartbeats 0",
       f"namespace {NS}","open BB6Coverage BB6Coverage.Agent31Pump"]

def table():
    s=header(["SweepPumping"])
    s.append("def table : PartialMachine := fun s => match s.1.val,s.2 with")
    for i,m in enumerate(M):
        if m=="---":continue
        s.append(f"  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(m[0]=='1').lower()},{str(m[1]=='R').lower()},{ord(m[2])-65}⟩)")
    s += ["  | _,_ => none",f"end {NS}",""]
    return "\n".join(s)

def batches(snaps,n):
    out=[]
    for k,lo in enumerate(range(0,len(snaps)-1,n)):
        hi=min(lo+n,len(snaps)-1)
        s=header(["F1ExposureTable"])
        for i in range(lo,hi):
            t,z=snaps[i];u,w=snaps[i+1]
            s += [f"theorem part{i:04d} : run0 table {u-t} {expr(z)} =",
                  f"    some {expr(w)} := by rfl"]
        s += [f"theorem block{k:03d} :",
             f"    run0 table {snaps[hi][0]-snaps[lo][0]} {expr(snaps[lo][1])} =",
             f"    some {expr(snaps[hi][1])} := by"]
        for i in range(lo,hi):
            s.append(f"  have h{i} := "+(f"part{i:04d}" if i==lo else f"join0 h{i-1} part{i:04d}"))
        s += [f"  simpa only [Nat.reduceAdd] using h{hi-1}",
              f"#print axioms block{k:03d}",f"end {NS}",""]
        out.append((f"F1ExposureBlock{k:03d}.lean","\n".join(s)))
    return out

def root(snaps,k):
    s=header([*[f"F1ExposureBlock{i:03d}" for i in range(k)],
              "Run0ExposureBound","FastZipWeight","Lean.Elab.Tactic.Omega"])
    s += ["open BB6Coverage.Agent10ZipAudit",
          "open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot",
          "open BB6.Agent29FastZipWeight BB6.Agent7D100ExposureBridge",
          f"def finalConfig : Z0 := {expr(snaps[-1][1])}",
          "theorem reached : run0 table 4672258 ⟨0,[],[]⟩ = some finalConfig := by"]
    for i in range(k):
        s.append(f"  have h{i} := "+(f"block{i:03d}" if i==0 else f"join0 h{i-1} block{i:03d}"))
    s += [f"  simpa [finalConfig] using h{k-1}",
          "theorem hole : table (5,true) = none := by decide",
          "theorem hroot : table initialSlot = some (some ⟨true,true,1⟩) := by decide",
          "theorem hno : weightedTNFNoAssignedHalt table := by",
          "  intro s","  rcases s with ⟨q,b⟩",
          "  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
          "  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide",
          "theorem query : zipRead table 4672258 = some (5,true) := by",
          "  simpa [finalConfig] using (zipRead_of_run0 table 4672258 finalConfig reached)",
          "theorem hrest : restOK table (5,true) = true := by decide",
          "theorem hweight : weightOK table (5,true) 4672258 4672264 = true :=",
          "  weightOK_of_slack table (5,true) 4672258 4672264 (by omega)",
          "theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 4672264 m :=",
          "  bounded_of_query table 4672258 4672264 (5,true)",
          "    query hroot hno hole hweight hrest m hm",
          "#print axioms reached","#print axioms hole","#print axioms bound",
          f"end {NS}",""]
    return "\n".join(s)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--chunk",type=int,default=2400)
    p.add_argument("--batch",type=int,default=30)
    a=p.parse_args()
    if a.chunk<=0 or a.batch<=0:p.error("positive chunk/batch required")
    snaps,info=scan(a.chunk)
    modules=[("F1ExposureTable.lean",table())]
    blocks=batches(snaps,a.batch)
    modules+=blocks+[("F1ExposureBound.lean",root(snaps,len(blocks)))]
    a.out.mkdir(parents=True,exist_ok=True);hashes={}
    for name,source in modules:
        (a.out/name).write_text(source)
        hashes[name]=hashlib.sha256(source.encode()).hexdigest()
    info.update(chunk=a.chunk,batch=a.batch,segment_count=len(snaps)-1,
                source_modules=len(modules),source_sha256=hashes)
    (a.out/"certificate.json").write_text(json.dumps(info,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:v for k,v in info.items() if k!="source_sha256"},sort_keys=True))
if __name__=="__main__":main()
