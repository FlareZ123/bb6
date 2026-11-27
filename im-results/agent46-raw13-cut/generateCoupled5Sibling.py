"""Candidate bank -> independent rowwise BiDFA + canonical four-hole sibling proof."""
import json, subprocess, sys
import generateCoupled4 as coupled4
from pathlib import Path
from collections import Counter
from generate import D, MOVES, boolean, move, slot, tally, emit as leaf_emit
from generate_branch_base import emit_base
from generateOneFAR import codes, fmt, saturate
from shard_cut import checked_subtree
sys.path.insert(0,str(D.parent/"agent32-raw59"))
from emit_rungram import emit as emit_bidfa

ROOT="1RB1LD1RC---1LA1RE---0LA---0RD------"
B=1007

def main(mv):
    global B
    assert mv in MOVES and mv!="1LF"
    data=json.loads((D/f"coupled5-{mv}.json").read_text())
    assert data["move"]==mv
    late={x["table"]:x for x in data["last"]}
    B=10007 if late else 1007
    coupled4.B=B
    assert all(x["holes"]==1 and x["n"]+6<=B for x in late.values())
    manual={"1RB1LD1RC1RA1LA1RE0LC0LA0RF0RD---1RC":"BB6.Agent46Raw13Coupled5Hard0LC"} if mv=="0LC" else {}
    if mv=="1LC":
        manual["1RB1LD1RC1RD1LA1RE1LC0LA1RF0RD---0RA"]="BB6.Agent46Raw13Coupled5Hard1LCrd"
    extras=json.loads((D/"coupled5-extra-bidfa.json").read_text())
    records=data["certs"]+[x for x in extras if x["table"] in data["unresolved"]]
    assert set(data["unresolved"])==set(manual)|{x["table"] for x in extras if x["table"] in data["unresolved"]}
    names={x["table"]:i for i,x in enumerate(records)}
    assert len(names)==len(records) and set(names)|set(manual)|set(late)==set(data["open"])
    raw=ROOT[:18]+mv+ROOT[21:]
    cut=max(5,ord(mv[-1])-64)
    mod="Raw13Coupled5Sibling"+mv.replace("0","Zero").replace("1","One")
    ns="BB6."+mod
    nsb=ns+"BiDFA"
    qry,qs=emit_base(raw,mod,D/(mod+"Base.lean"),holes=4)
    src=["import FastBiDFA","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
         "namespace "+nsb,"open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA"]
    for i,x in enumerate(records):
        src.append(emit_bidfa(i,x["table"],*x["dfa"],[x["states"],x["edges"]]))
    src.append("end "+nsb)
    (D/(mod+"BiDFA.lean")).write_text("\n".join(src)+"\n")
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
    z=json.loads(subprocess.check_output(["node","-e",node,str(D/"scanCoupled5.js"),
         str(D/"frontier-dfa-bank.txt"),str(D/f"coupled5-{mv}.json"),str(MOVES.index(mv))],text=True))
    tree=z["tree"]
    assert not z["open"] and tree[:3]==["split",qry,qs] and z["max_query"]+6<=B
    cnt,mass=Counter(),Counter();tally(tree,4,cut,cnt,mass)
    assert sum(mass.values())==25**4 and not cnt["open"] and cnt["auto"]==len(records)+len(manual)+len(late)
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
                p=manual[v[0]]
                return f".closed (.proven {p}.p {p}.never)"
            p=f"{nsb}.M{names[v[0]]}"
            return f".closed (.proven {p}.table {p}.never)"
        if tag=="split":
            n,s,kids=v
            return f".split {n} {slot(s)} (byCutMove [\n"+",\n".join(map(emit,kids))+"])"
        assert tag in ("cycle","state","last"),tag
        return leaf_emit(t)
    # Use composition rather than kernel normalization of the whole tree.
    body=checked_subtree(tree,"Root","parent",cut,B,emit,complete=True)
    body+=f"""
def parentCut : Cut := cRoot
theorem parent_checked : check {B} parent {cut} parentCut = true := okRoot
theorem empty_complement : residuals parent {cut} parentCut = [] :=
  residuals_empty_of_closedCut completeRoot
theorem bound (m : Machine) (hm : compatible parent m) : WeightedBound {B} m := by
  rcases sound {B} parent {cut} parentCut (by decide) parent_support (by decide)
      parent_nohalt parent_checked m (compatible_quotient m hm) with hb | ⟨e,he,hq⟩
  · exact hb
  · rw [empty_complement] at he
    simp at he
#print axioms parent_checked
#print axioms empty_complement
#print axioms bound
"""
    (D/(mod+".lean")).write_text(("".join("import "+x.split(".")[-1].replace("Agent46","")+"\n" for x in sorted(set(manual.values()))))+("import "+mod+"Late\n" if late else "")+f"import {mod}Base\nimport {mod}BiDFA\nimport Agent46CompleteCut\n"
        f"set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\n"
        "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut\n"+body+f"\nend {ns}\n")
    return mod
if __name__=="__main__":
    modules=[main(mv) for mv in sys.argv[1:]]
    assert modules
    (D/"Raw13Coupled5SiblingBundle.lean").write_text("".join(f"import {m}\n" for m in modules))
