#!/usr/bin/env python3
"""Produce source-checkable exact 2396150-step opaque-tail pumping certificates.
Partial table 1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC.
Untrusted producer; only successful original-source Lean audit proves NeverHalts.
"""
from __future__ import annotations
from collections import deque
import argparse, hashlib, json
from pathlib import Path

TABLE="1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC"
MOVE=[TABLE.replace("_","")[3*i:3*i+3] for i in range(12)]
PRE="0111"+"0"*11
BLOCK="000000000000001111111111111111111111111111111111111111111111111111111011101111"
PERIOD=2396150
NS="BB6.Agent7D100LongEpoch"
assert len(PRE)==15 and len(BLOCK)==78 and BLOCK.count("1")==62

def bits(x):
    return "["+",".join("true" if c=="1" else "false" for c in x)+"]"

def exp(z,symbolic):
    q,l,r=z
    if symbolic:
        assert l.endswith("?") and l.count("?")==1 and "?" not in r
        return f"⟨{q},{bits(l[:-1])}++T,{bits(r)}⟩"
    assert "?" not in l+r
    return f"⟨{q},{bits(l)},{bits(r)}⟩"

def trace(start,steps,chunk):
    q,ls,rs=start;L=deque(ls);R=deque(rs)
    snaps=[(0,start)];low=len(ls);high=len(ls)
    for t in range(1,steps+1):
        v=L[0] if L else "0"
        if v not in "01": raise ValueError(f"opaque suffix read at step {t-1}")
        mv=MOVE[2*q+int(v)]
        if mv=="---": raise ValueError(f"undefined transition queried at {t-1}")
        w,d,j=mv
        if d=="L":
            if L:L.popleft()
            R.appendleft(w)
        else:
            b=R.popleft() if R else "0"
            if b not in "01":raise ValueError(f"opaque right suffix read {t-1}")
            if L:L.popleft()
            L.appendleft(w);L.appendleft(b)
        q=ord(j)-65
        if start[1].endswith("?"):
            if not L or L[-1]!="?" or L.count("?")!=1:
                raise ValueError(f"unknown suffix altered at step {t}")
            low=min(low,len(L)-1);high=max(high,len(L)-1)
        if t%chunk==0 or t==steps:
            snaps.append((t,(q,"".join(L),"".join(R))))
    return snaps,dict(low=low,high=high)

def generate(chunk,batch):
    entry,_=trace((0,"",""),12,12)
    assert entry[-1][1]==(0,"0111","0"),entry[-1]
    base,bd=trace(entry[-1][1],PERIOD,chunk)
    sym,sd=trace((0,PRE+"?","0"),PERIOD,chunk)
    assert base[-1][1]==(0,PRE+BLOCK,"0"),base[-1][1]
    assert sym[-1][1]==(0,PRE+BLOCK+"?","0"),sym[-1][1]
    assert sd["low"]>=1 and len(base)==len(sym)
    assert all(x[0]==y[0] for x,y in zip(base,sym))
    return base,sym,dict(entry=12,period=PERIOD,pre=PRE,block=BLOCK,
        block_ones=BLOCK.count("1"),base=bd,opaque=sd,chunk=chunk,batch=batch)

def header(imports):
    return [*(f"import {name}" for name in imports),
        "set_option maxRecDepth 100000","set_option maxHeartbeats 0",
        f"namespace {NS}","open BB6Coverage BB6Coverage.Agent31Pump"]

def table_source():
    s=header(["SweepPumping"])
    s.append("def table : PartialMachine := fun s => match s.1.val,s.2 with")
    for i,m in enumerate(MOVE):
        if m=="---":continue
        s.append(f"  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(m[0]=='1').lower()},{str(m[1]=='R').lower()},{ord(m[2])-65}⟩)")
    s += ["  | _,_ => none",f"def pre : List Bool := {bits(PRE)}",
         f"def block : List Bool := {bits(BLOCK)}",
         "def family (n : Nat) : Z0 := ⟨0,pre ++ rep block (n+1),[false]⟩",
         "theorem entry12 : run0 table 12 ⟨0,[],[]⟩ =",
         "    some ⟨0,[false,true,true,true],[false]⟩ := by rfl",
         f"end {NS}",""]
    return "\n".join(s)

def groups(prefix,snaps,batch,symbolic):
    result=[]
    for group,start in enumerate(range(0,len(snaps)-1,batch)):
        stop=min(start+batch,len(snaps)-1)
        s=header(["LongEpochTable"])
        for i in range(start,stop):
            t0,z0=snaps[i];t1,z1=snaps[i+1]
            p="(T : List Bool)" if symbolic else ""
            s += [f"theorem {prefix}_part{i:04d} {p} :",
                  f"    run0 table {t1-t0} {exp(z0,symbolic)} =",
                  f"    some {exp(z1,symbolic)} := by rfl"]
        p="(T : List Bool)" if symbolic else ""
        s += [f"theorem {prefix}_block{group:03d} {p} :",
              f"    run0 table {snaps[stop][0]-snaps[start][0]} {exp(snaps[start][1],symbolic)} =",
              f"    some {exp(snaps[stop][1],symbolic)} := by"]
        for i in range(start,stop):
            a=f"{prefix}_part{i:04d}"+(" T" if symbolic else "")
            if i==start:s.append(f"  have h{i} := {a}")
            else:s.append(f"  have h{i} := join0 h{i-1} ({a})")
        s += [f"  simpa only [Nat.reduceAdd] using h{stop-1}",f"end {NS}",""]
        result.append((f"LongEpoch{prefix.capitalize()}{group:03d}.lean","\n".join(s)))
    return result

def root_source(nb,ns):
    s=header([*[f"LongEpochBase{i:03d}" for i in range(nb)],
              *[f"LongEpochSym{i:03d}" for i in range(ns)]])
    s += ["theorem base : run0 table 2396150 ⟨0,[false,true,true,true],[false]⟩ =",
          "    some ⟨0,pre ++ block,[false]⟩ := by"]
    for i in range(nb):
        s.append(f"  have h{i} := "+(f"base_block{i:03d}" if i==0 else f"join0 h{i-1} base_block{i:03d}"))
    s += [f"  simpa [pre,block] using h{nb-1}",
          "theorem one (T : List Bool) :",
          "    run0 table 2396150 ⟨0,pre ++ T,[false]⟩ =",
          "    some ⟨0,pre ++ block ++ T,[false]⟩ := by"]
    for i in range(ns):
        s.append(f"  have g{i} := "+(f"sym_block{i:03d} T" if i==0 else f"join0 g{i-1} (sym_block{i:03d} T)"))
    s += [f"  simpa [pre,block] using g{ns-1}",
          "theorem entry : run0 table 2396162 ⟨0,[],[]⟩ = some (family 0) := by",
          "  have h := join0 entry12 base",
          "  simpa [family,rep] using h",
          "theorem growth (n : Nat) :",
          "    run0 table 2396150 (family n) = some (family (n+1)) := by",
          "  have h := one (rep block (n+1))",
          "  simpa only [family,rep,List.append_assoc] using h",
          "theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=",
          "  never_of_growth table family 2396162 (fun _ => 2396150)",
          "    entry (by intro _; decide) growth m hm",
          "#print axioms base","#print axioms one",
          "#print axioms entry","#print axioms growth","#print axioms never",
          f"end {NS}",""]
    return "\n".join(s)

def emit(out,chunk,batch):
    base,sym,info=generate(chunk,batch)
    src=[("LongEpochTable.lean",table_source())]
    bb=groups("base",base,batch,False)
    sb=groups("sym",sym,batch,True)
    src+=bb+sb+[("LongEpochNever.lean",root_source(len(bb),len(sb)))]
    out.mkdir(parents=True,exist_ok=True)
    hashes={}
    for name,s in src:
        (out/name).write_text(s)
        hashes[name]=hashlib.sha256(s.encode()).hexdigest()
    info.update(files=len(src),hashes=hashes)
    (out/"certificate.json").write_text(json.dumps(info,indent=2,sort_keys=True)+"\n")
    return info

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path)
    p.add_argument("--chunk",type=int,default=1200)
    p.add_argument("--batch",type=int,default=36)
    a=p.parse_args()
    if a.chunk<=0 or a.batch<=0:p.error("positive chunk/batch required")
    info=emit(a.out,a.chunk,a.batch) if a.out else generate(a.chunk,a.batch)[2]
    print(json.dumps({k:v for k,v in info.items() if k!="hashes"},sort_keys=True))
if __name__=="__main__": main()
