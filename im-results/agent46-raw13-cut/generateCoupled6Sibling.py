"""Candidate bank -> independent rowwise BiDFA + canonical five-hole sibling proof."""
import json, subprocess, sys
from itertools import product
import generateCoupled4 as coupled4
from pathlib import Path
from collections import Counter
from generate import D, MOVES, boolean, move, slot, tally, emit as leaf_emit
from generate_branch_base import emit_base
from generateOneFAR import codes, fmt, saturate
from shard_cut import checked_subtree
sys.path.insert(0,str(D.parent/"agent32-raw59"))
from emit_rungram import emit as emit_bidfa

ROOT="1RB1LD1RC---1LA1RE---0LA------------"
B=1007

def main(mv):
    global B
    assert mv in MOVES and mv not in ("0RD","0RA","1LC")
    data=json.loads((D/f"coupled6-{mv}.json").read_text())
    assert data["move"]==mv
    late={x["table"]:x for x in data["last"]}
    manual={}
    extra_imports=[]
    if mv=="1LB":
        ns_late="BB6.Agent46Raw13Coupled6Late1LB"
        ns_nested="BB6.Agent46Raw13Coupled6Nested1LB"
        extra_imports=["Raw13Coupled6Late1LBBound","Raw13Coupled6Nested1LB"]
        for d,t in [("false","1RB1LD1RC1RA1LA1RE0LC0LA0RF1LB---0LC"),
                    ("true","1RB1LD1RC1RA1LA1RE1LE0LA0RF1LB---0LC")]:
            manual[t]=f".bounded ({ns_late}.p {d}) 2651340 ({ns_late}.bound {d})"
        for d,t in [("false","1RB1LD1RC0RF1LA1RE1LA0LA---1LB0LC0RB"),
                    ("true","1RB1LD1RC0RF1LA1RE1LA0LA---1LB0LD0RB")]:
            manual[t]=f".closed (.proven ({ns_nested}.p {d}) ({ns_nested}.never {d}))"
    if mv in ("1LD","1RD"):
        ns="BB6.Agent46Raw13Coupled6LateCore"
        extra_imports=["Raw13Coupled6LateCoreBound"]
        if mv=="1LD":
            for d,t in [("false","1RB1LD1RC1RA1LA1RE0LC0LA0RF1LD---0LC"),
                        ("true","1RB1LD1RC1RA1LA1RE1LE0LA0RF1LD---0LC")]:
                manual[t]=f".bounded ({ns}.Dtab {d}) 2651346 ({ns}.boundD {d})"
        else:
            manual["1RB1LD1RC1RA1LA1RE1LE0LA0RF1RD---0LC"]=f".bounded {ns}.Rtab 2651346 {ns}.boundR"
            extra_imports+=["Raw13Coupled6RDSweep","Raw13Coupled6RDAlt"]
            ns_sweep="BB6.Agent46Raw13Coupled6RDSweep"
            ns_alt="BB6.Agent46Raw13Coupled6RDAlt"
            for d,f,t in [("false","false","1RB1LD1RC1RA1LA1RE0LF0LA0RB1RD---1RC"),
                          ("true","false","1RB1LD1RC1RA1LA1RE1LF0LA0RB1RD---1LB"),
                          ("true","true","1RB1LD1RC1RA1LA1RE1LF0LA0RB1RD---1LD")]:
                manual[t]=f".closed (.proven ({ns_sweep}.p {d} {f}) ({ns_sweep}.never {d} {f}))"
            manual["1RB1LD1RC0RD1LA1RE1LB0LA1RF1RD---1RA"]=f".closed (.proven {ns_alt}.p {ns_alt}.never)"
    B=max(62123,2651340 if mv=="1LB" else 2651346 if mv in ("1LD","1RD") else 0,max((x['n']+6 for x in late.values()),default=0))
    coupled4.B=B
    assert all(x["holes"]==1 and x["n"]+6<=B for x in late.values())
    # Additional literal witnesses can be deposited independently.
    extra_file=D/"coupled6-extra-bidfa.json"
    extras=json.loads(extra_file.read_text()) if extra_file.exists() else []
    records=data["certs"]+[x for x in extras if x["table"] in data["unresolved"]]
    assert set(data["unresolved"])==set(manual)|{x["table"] for x in extras if x["table"] in data["unresolved"]}
    names={x["table"]:i for i,x in enumerate(records)}
    assert len(names)==len(records) and set(names)|set(manual)|set(late)==set(data["open"])
    raw=ROOT[:27]+mv+ROOT[30:]
    cut=max(5,ord(mv[-1])-64)
    mod="Raw13Coupled6Sibling"+mv.replace("0","Zero").replace("1","One")
    ns="BB6."+mod
    nsb=ns+"BiDFA"
    qry,qs=emit_base(raw,mod,D/(mod+"Base.lean"),holes=5)
    # Small modules preserve parallelism even for several hundred literal invariants.
    bmods=[]
    for first in range(0,len(records),24):
        bmod=mod+"BiDFA"+str(first//24)
        src=["import FastBiDFA","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
             "namespace "+nsb,"open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA"]
        for i,x in enumerate(records[first:first+24],first):
            src.append(emit_bidfa(i,x["table"],*x["dfa"],[x["states"],x["edges"]]))
        src.append("end "+nsb)
        (D/(bmod+".lean")).write_text("\n".join(src)+"\n")
        bmods.append(bmod)
    (D/(mod+"BiDFA.lean")).write_text("".join("import "+m+"\n" for m in bmods) or "import FastBiDFA\n")
    # The JS scanner only supplies data; every leaf is independently proved in Lean.
    node=r"""
const fs=require("fs");
const [file,bankFile,dataFile,x]=process.argv.slice(1);
const m=new Function(fs.readFileSync(file,"utf8"))();
const bank=fs.readFileSync(bankFile,"utf8").trim().split(/\s+/).map(s=>[...s].map(Number));
const data=JSON.parse(fs.readFileSync(dataFile,"utf8"));
const z=m.scan(Number(x),bank,new Set([...data.certs.map(x=>x.table),...data.unresolved,...data.last.map(x=>x.table)]));
console.log(JSON.stringify(z));
"""
    z=json.loads(subprocess.check_output(["node","-e",node,str(D/"scanCoupled6.js"),
         str(D/"frontier-dfa-bank.txt"),str(D/f"coupled6-{mv}.json"),str(MOVES.index(mv))],text=True))
    tree=z["tree"]
    assert not z["open"] and tree[:3]==["split",qry,qs] and z["max_query"]+6<=B
    cnt,mass=Counter(),Counter();tally(tree,5,cut,cnt,mass)
    assert sum(mass.values())==25**5 and not cnt["open"] and cnt["auto"]==len(records)+len(manual)+len(late)
    print(mv,cnt,mass,flush=True)
    lnames={t:i for i,t in enumerate(late)}
    if late:
        (D/(mod+"Late.lean")).write_text("import Agent46CompleteCut\n"+coupled4.HEADER.replace(coupled4.NS,ns)+"\n".join(coupled4.late_module(t,x["n"],x["slot"],lnames[t]) for t,x in late.items())+"\nend "+ns+"\n")
    def emit(t):
        if t is None:return ".unresolved"
        tag,*v=t
        if tag=="far":
            table,rev,df=v;dfa=list(map(int,df));a,b,k=saturate(codes(table),dfa,rev)
            return f".closed (.far {boolean(rev)} {len(dfa)//2} ⟨0,{fmt(dfa)},{fmt(a)},{fmt(b)},{k}⟩)"
        if tag=="auto":
            if v[0] in late:
                i=lnames[v[0]]
                return f".bounded L{i}.p {B} L{i}.bound"
            if v[0] in manual:
                return manual[v[0]]
            p=f"{nsb}.M{names[v[0]]}"
            return f".closed (.proven {p}.table {p}.never)"
        if tag=="split":
            n,s,kids=v
            return f".split {n} {slot(s)} (byCutMove [\n"+",\n".join(map(emit,kids))+"])"
        assert tag in ("cycle","state","last"),tag
        return leaf_emit(t)
    # Each root child is an independently elaborated proof module, as in
    # the six-hole catalogue. Do not concatenate all 50k+ nodes in one file.
    imports=[mod+"Base",mod+"BiDFA","Agent46CompleteCut"]+extra_imports
    if late: imports.append(mod+"Late")
    header="set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace "+ns+"\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut\n"
    def write(name,dependencies,body):
        (D/(name+".lean")).write_text("".join("import "+x+"\n" for x in dependencies)+header+body+"\nend "+ns+"\n")
    mods=[]
    for i,k in enumerate(tree[3]):
        if k is None:continue
        tag=f"{i:02}"
        name=mod+"Kid"+tag
        p=f"next {move(MOVES[i])}"
        decl=checked_subtree(k,tag,p,max(cut,i%6+1),B,emit,complete=True)
        write(name,imports,decl+f"\ndef kid{tag} : Cut := c{tag}\ntheorem checked{tag} : check {B} ({p}) (nextCut {cut} {move(MOVES[i])}) kid{tag} = true := ok{tag}\ntheorem closed{tag} : closedCut (nextCut {cut} {move(MOVES[i])}) kid{tag} = true := complete{tag}\n")
        mods.append(name)
    terms=",".join(f"kid{i:02}" if tree[3][i] is not None else ".unresolved" for i in range(24))
    cases="\n".join(f"  · exact checked{12*w+6*r+q:02}" for q,w,r in product(range(min(cut,5)+1),range(2),range(2)))
    ccases=cases.replace("exact checked","exact closed")
    qcases=" ∨ ".join(f"q = {i}" for i in range(min(cut,5)+1))
    rcases_q="|".join("rfl" for _ in range(min(cut,5)+1))
    write(mod,mods,f"""
def kids : Move → Cut := byCutMove [{terms}]
theorem kids_checked (mv : Move) (hv : mv.next.val ≤ {cut}) :
    check {B} (next mv) (nextCut {cut} mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ {cut} at hv
  have hq : {qcases} := by omega
  rcases hq with {rcases_q}
  all_goals cases w <;> cases r
{cases}
def parentCut : Cut := .split {qry} {slot(qs)} kids
theorem parent_checked : check {B} parent {cut} parentCut = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK {B} parent {qry} {slot(qs)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ {cut} then check {B} (next mv) (nextCut {cut} mv) (kids mv) else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  by_cases h : mv.next.val ≤ {cut}
  · simp [h,kids_checked mv h]
  · simp [h]
theorem kids_closed (mv : Move) (hv : mv.next.val ≤ {cut}) :
    closedCut (nextCut {cut} mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ {cut} at hv
  have hq : {qcases} := by omega
  rcases hq with {rcases_q}
  all_goals cases w <;> cases r
{ccases}
theorem parent_closed : closedCut {cut} parentCut = true := by
  simp only [parentCut,closedCut]
  apply BB6.Agent31ThreeHole.allMoves_of
  intro mv
  by_cases hv : mv.next.val ≤ {cut}
  · simp [hv,kids_closed mv hv]
  · simp [hv]
theorem empty_complement : residuals parent {cut} parentCut = [] :=
  residuals_empty_of_closedCut parent_closed
theorem bound (m : Machine) (hm : compatible parent m) : WeightedBound {B} m := by
  rcases sound {B} parent {cut} parentCut (by decide) parent_support (by decide)
      parent_nohalt parent_checked m (compatible_quotient m hm) with hb | ⟨e,he,hq⟩
  · exact hb
  · rw [empty_complement] at he
    simp at he
#print axioms parent_checked
#print axioms empty_complement
#print axioms bound
""")
    return mod
if __name__=="__main__":
    modules=[main(mv) for mv in sys.argv[1:]]
    assert modules
    (D/"Raw13Coupled6SiblingBundle.lean").write_text("".join(f"import {m}\n" for m in modules))
