#!/usr/bin/env python3
"""Generate checkable complete/partial weighted audits for the q32 queue slice.

Discovery is untrusted. Every accepted classification must pass the existing
Lean zipCheck/partialCheck. Unresolved leaves are never discarded.
"""
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
IM = HERE.parent
ORDER = [4*q+2*w+r for w,r,q in product(range(2),range(2),range(6))]
B = 144

def parse(text):
    xs = text.replace("_", "")
    assert len(xs) == 36
    return tuple(-1 if a=="---" else
                 4*"ABCDEF".index(a[2])+2*int(a[0])+int(a[1]=="R")
                 for a in (xs[i:i+3] for i in range(0,36,3)))

def fmt(p):
    xs = ["---" if a<0 else f"{(a>>1)&1}{'R' if a&1 else 'L'}{'ABCDEF'[a>>2]}" for a in p]
    return "_".join("".join(xs[i:i+2]) for i in range(0,12,2))

def refines(p, q):
    return all(b<0 or a==b for a,b in zip(p,q))

def source_roster():
    q = (IM/"agent8-adaptive-source-plan/Agent8PackedChunk2_32_32.v").read_text()
    s = (IM/"agent47-rooted-tnf/Agent47SourceChunk2.v").read_text()
    rows = [parse(x) for x in re.findall(r'\("([01LR A-F_-]+)",\s*\d+,\s*\d+\)',q)]
    side = [parse(x) for x in re.findall(r'\("([01LR A-F_-]+)",\s*SWside',s)]
    sweep = [parse("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---"+a+"_------") for a in ("1RB","0RC")]
    assert len(rows)==84 and len(set(rows))==84 and len(side)==32
    parent=parse("1RB---_1RC---_0LA---_------_------_------")
    assert all(refines(p,parent) for p in rows)
    old=[p for p in rows if any(refines(p,q) for q in side+sweep)]
    todo=[p for p in rows if p not in old]
    assert len(old)==34 and len(todo)==50
    assert [p.count(-1) for p in todo[:12]]==[3]*9+[4]*3
    return rows,old,todo

def classify(p,limit=1000,max_period=256):
    # l is left half excluding head; r is right half including head.
    l=r=q=h=0
    pos=[]; cfg=[]
    rb=defaultdict(list); lb=defaultdict(list)
    for t in range(limit+1):
        cfg.append((q,l,r)); pos.append(h)
        cur=r&1; s=2*q+cur; a=p[s]
        if a<0:
            return ("hole",t,s)
        for direction,bucket,key in ((1,rb,(q,r)),(-1,lb,(q,cur,l))):
            earlier=bucket[key]
            for e in reversed(earlier):
                if t-e>max_period: break
                if direction*(h-pos[e])<0: continue
                k=max(0,max(direction*(pos[e]-x) for x in pos[e:t+1]))
                aa,bb=(cfg[e][1],l) if direction==1 else (cfg[e][2]>>1,r>>1)
                if ((aa^bb)&((1<<k)-1))==0:
                    return ("cycle",e,t-e,direction==1,pos[e]-direction*k)
            earlier.append(t)
        if t==limit: break
        w=(a>>1)&1; q=a>>2
        if a&1:
            l=(l<<1)|w; r>>=1; h+=1
        else:
            r=((r>>1)<<2)|(w<<1)|(l&1); l>>=1; h-=1
    return ("open",)

def canonical_dfas(d):
    def rec(a,mx):
        if len(a)==2*d:
            if mx==d-1: yield tuple(a)
            return
        if len(a)//2>mx: return
        for j in range(min(d-1,mx+1)+1):
            yield from rec(a+[j],max(j,mx))
    return rec([0],0)

DFAS=[(rev,D) for d in range(1,5) for D in canonical_dfas(d) for rev in (0,1)]

def far(p,rev,D):
    # Same finite saturation conditions as the established FastFAR generator.
    d=len(D)//2; N=6*d+1; H=N-1; halt=1<<H
    T=[0]*(2*N); T[H]=T[N+H]=halt; rules=[]
    for l,q,a in product(range(d),range(6),range(2)):
        mv=p[2*q+a]; dst=a*N+6*l+q
        if mv<0:
            T[dst]=halt
            continue
        w=(mv>>1)&1; r=mv&1; nxt=mv>>2
        if r!=rev:
            T[dst]=1<<(6*D[2*l+w]+nxt)
        else:
            for j,b in product(range(d),range(2)):
                if D[2*j+b]==l:
                    rules.append((dst,b*N+6*j+nxt,w*N))
    while True:
        z=halt
        while True:
            zz=z
            for j in range(N):
                if T[j]&z: z|=1<<j
            if z==zz: break
        if z&1: return None
        changed=False
        for dst,src,off in rules:
            v=T[dst]; bits=T[src]
            while bits:
                b=bits&-bits; v|=T[off+b.bit_length()-1]; bits^=b
            if v!=T[dst]:
                T[dst]=v; changed=True
        if not changed: return d,list(D),T[:N],T[N:],z

def build(p,stats,unresolved):
    c=classify(p)
    typ=c[0]
    if typ=="cycle":
        stats["cycle"]+=1
        return c
    if typ=="open":
        for rev,D in DFAS:
            cert=far(p,rev,D)
            if cert is not None:
                stats["far"]+=1
                return ("far",rev,cert)
        stats["open"]+=1
        unresolved.append(p)
        return ("open",p)
    _,n,s=c
    stats["max_n"]=max(stats["max_n"],n)
    assert n+6<=B
    if p.count(-1)==1:
        stats["last"]+=1
        return ("last",n,s)
    stats["split"]+=1
    return ("split",n,s,[build(p[:s]+(a,)+p[s+1:],stats,unresolved) for a in range(24)])

def boolean(x): return str(bool(x)).lower()
def slot(s): return f"({s//2},{boolean(s%2)})"
def move(a): return f"⟨{boolean(a&2)},{boolean(a&1)},{a>>2}⟩"
def table(p):
    return "fun s => match s.1.val, s.2 with\n"+ "".join(
        f"  | {i//2}, {boolean(i%2)} => some (some {move(a)})\n"
        for i,a in enumerate(p) if a>=0)+"  | _, _ => none"

def closed(t):
    return t[0]!="open" and (t[0]!="split" or all(closed(k) for k in t[3]))

def audit(t):
    typ=t[0]
    if typ=="cycle":
        _,e,k,r,b=t
        return f".cycle {e} {k} {boolean(r)} ({b})"
    if typ=="far":
        _,rev,(d,D,L,R,z)=t
        return f".far {boolean(rev)} {d} ⟨0,{D},{L},{R},{z}⟩"
    if typ=="last":
        return f".last {t[1]} {slot(t[2])}"
    assert typ=="split"
    return f".split {t[1]} {slot(t[2])} (byMove ["+",\n".join(audit(t[3][a]) for a in ORDER)+"])"

def partial(t):
    if closed(t): return ".closed ("+audit(t)+")"
    if t[0]=="open": return ".unresolved"
    return f".split {t[1]} {slot(t[2])} (byPartialMove ["+",\n".join(partial(t[3][a]) for a in ORDER)+"])"

HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Q32Slice
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent50TNFPilot BB6.Agent8TNFPath BB6.Agent10ZipAudit
open BB6.Agent47PartialAudit
"""
def emit(name,imports,body):
    (HERE/(name+".lean")).write_text("".join(f"import {m}\n" for m in imports)+HEADER+body+"\nend BB6.Agent44Q32Slice\n",encoding="utf-8")

def base(i,p):
    return f"""def p{i} : PartialMachine := {table(p)}
theorem root{i} : p{i} initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt{i} : weightedTNFNoAssignedHalt p{i} := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases b <;> decide
"""

def emit_one(i,p,t,res):
    mod=f"Q32Slice{i:02}"
    n=len(res)
    if i<9:
        assert not n
        emit(mod,["ZipPrefixAudit","PartialAudit"],base(i,p)+f"""
def audit{i} : Audit := {audit(t)}
theorem checked{i} : zipCheck {B} p{i} audit{i} = true := by
  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]
  decide
theorem safe{i} : ∀ m, compatible p{i} m → WeightedBound {B} m :=
  (certifiedZip {B} p{i} audit{i} root{i} nohalt{i} checked{i}).sound
#print axioms safe{i}
""")
        return mod
    # A large root is assembled from independent first-hole children. Every
    # branch is present; partial leaves remain part of partialResiduals.
    assert t[0]=="split"
    _,tn,s,children=t
    parentmod=mod+"Base"
    emit(parentmod,["ZipPrefixAudit","PartialAudit"],base(i,p)+f"""
abbrev child{i} (mv : Move) := refine p{i} {slot(s)} (some mv)
theorem query{i} : zipQueryOK {B} p{i} {tn} {slot(s)} = true := by decide
""")
    mods=[]
    for j,a in enumerate(ORDER):
        k=children[a]
        name=mod+f"K{j:02}"
        mods.append(name)
        if closed(k):
            body=f"""def sub{i}_{j} : Audit := {audit(k)}
def kid{i}_{j} : PartialAudit := .closed sub{i}_{j}
theorem check{i}_{j} : partialCheck {B} (child{i} {move(a)}) kid{i}_{j} = true := by
  change zipCheck {B} (child{i} {move(a)}) sub{i}_{j} = true
  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]
  decide
"""
        else:
            body=f"""def kid{i}_{j} : PartialAudit := {partial(k)}
theorem check{i}_{j} : partialCheck {B} (child{i} {move(a)}) kid{i}_{j} = true := by decide
"""
        emit(name,[parentmod],body)
    cases="\n".join(f"  · exact check{i}_{12*w+6*r+q}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""def kids{i} : Move → PartialAudit := byPartialMove [{','.join(f'kid{i}_{j}' for j in range(24))}]
theorem kids_checked{i} (mv : Move) : partialCheck {B} (child{i} mv) (kids{i} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def audit{i} : PartialAudit := .split {tn} {slot(s)} kids{i}
theorem checked{i} : partialCheck {B} p{i} audit{i} = true := by
  change (zipQueryOK {B} p{i} {tn} {slot(s)} && allMoves (fun mv => partialCheck {B} (child{i} mv) (kids{i} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query{i}, allMoves_of _ kids_checked{i}⟩
theorem coverage{i} : ∀ m, compatible p{i} m → WeightedBound {B} m ∨
    ∃ e ∈ partialResiduals p{i} audit{i}, compatible e.2 m :=
  partialSound {B} p{i} audit{i} root{i} nohalt{i} checked{i}
theorem remaining_count{i} : (partialResiduals p{i} audit{i}).length = {n} := by decide
#print axioms coverage{i}
#print axioms remaining_count{i}
"""
    if not n:
        body+=f"""theorem safe{i} : ∀ m, compatible p{i} m → WeightedBound {B} m := by
  intro m hm
  rcases coverage{i} m hm with h | ⟨e,he,_⟩
  · exact h
  · have hn : partialResiduals p{i} audit{i} = [] := List.length_eq_zero_iff.mp remaining_count{i}
    simp [hn] at he
#print axioms safe{i}
"""
    emit(mod,mods,body)
    return mod

def main():
    rows,old,todo=source_roster()
    records=[]; mods=[]
    for i,p in enumerate(todo[:12]):
        st=Counter(); res=[]
        t=build(p,st,res)
        assert len(res)==([0]*9+[5,0,9])[i],(i,st)
        mods.append(emit_one(i,p,t,res))
        records.append({"index":i,"table":fmt(p),"queue_index":rows.index(p),
                        "counts":dict(st),"residuals":[fmt(x) for x in res]})
        print(i,fmt(p),dict(st),flush=True)
    # Each complete source cylinder is exported individually. This aggregate
    # proves a disjunction over the ten exact input tables, not over raw11.
    safe_ids=list(range(9))+[10]
    cases="\n".join(f"  · exact safe{i} m hc" for i in safe_ids)
    emit("Q32SliceData",mods,f"""
def closedTables : List PartialMachine := [{','.join(f'p{i}' for i in safe_ids)}]
theorem closedTables_sound : ∀ p ∈ closedTables, ∀ m, compatible p m → WeightedBound {B} m := by
  intro p hp m hc
  simp only [closedTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {'|'.join('rfl' for _ in safe_ids)}
{cases}
#print axioms closedTables_sound
""")
    manifest={"bound":B,"queue":[fmt(p) for p in rows],
              "old_source_certificates":[fmt(p) for p in old],
              "audited":records,"untouched":[fmt(p) for p in todo[12:]]}
    (HERE/"Q32SliceManifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    assert sum(len(x["residuals"]) for x in records)==14

if __name__=="__main__":
    main()
