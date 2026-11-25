"""Extend the raw110 cut through six remaining first-hole branches.

All search outputs are untrusted. Every retained closed subtree must pass
the same zipCheck/partialCheck and every unresolved leaf stays in the cut.
The bank contains only previously discovered FAR candidates; no stochastic
search or exhaustive DFA enumeration is repeated.
"""
from pathlib import Path
from collections import Counter
from dataclasses import dataclass
from itertools import product
import hashlib, json, subprocess, tempfile, sys

ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/x) for x in ("agent31-three-hole-tnf","agent10-tnf-multipump","agent1-ngram")]
import generate_sweeps as one
from generate_four_hole import masks, move, slot
import multi
import emit_ngram

spec=json.loads((ROOT/"partial_spec.json").read_text())
PARENT=one.parse("1RB---_1RC---_0RD---_1LD1RE_---0LC_------")
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
B=7014
NS="BB6.Agent7Raw110"
HEADER=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name,imports,lines):
    (ROOT/(name+".lean")).write_text("".join(f"import {i}\n" for i in imports)+HEADER+"\n".join(lines)+f"\nend {NS}\n")

@dataclass
class Node:
    head: str
    children: list | None = None
    size: int = 1
    open_count: int = 0

def render(n):
    if n.children is None:
        return n.head
    if n.open_count==0:
        return n.head+" (byMove [\n"+",\n".join(render(k) for k in n.children)+"])"
    return n.head+" (byPartialMove [\n"+",\n".join(render_partial(k) for k in n.children)+"])"

def render_partial(n):
    return "(.closed ("+render(n)+"))" if n.open_count==0 else render(n)

def build_module(node,p,rootname,imports,limit=180,shardlimit=9000):
    """Chunk proofs structurally. Closed regions stay Audit so residual
    extraction never visits their certificate data."""
    shards=[]
    def local(n,p,name,code):
        partial=n.open_count!=0
        ty="PartialAudit" if partial else "Audit"
        checker="partialCheck" if partial else "zipCheck"
        if n.size<=limit:
            code.append(f"def {name} : {ty} := {render(n)}\ntheorem {name}_checked : {checker} {B} {p} {name} = true := by rfl\n")
            return
        n0,s0=n.head.removeprefix(".split ").split(" ",1)
        child_names=[]
        for j,k in enumerate(n.children):
            kname=f"{name}_k{j:02}"
            kp=f"(refine {p} {s0} (some {move(MOVES[j])}))"
            local(k,kp,kname,code)
            child_names.append(kname if not partial or k.open_count else f"(.closed {kname})")
        bymove="byPartialMove" if partial else "byMove"
        kidexpr=f"({bymove} ["+",".join(child_names)+"])"
        code.append(f"def {name} : {ty} := {n.head} {kidexpr}\ntheorem {name}_checked : {checker} {B} {p} {name} = true := by")
        code.append(f"  change (zipQueryOK {B} {p} {n0} {s0} && allMoves (fun mv => {checker} {B} (refine {p} {s0} (some mv)) ({kidexpr} mv))) = true")
        code.append("""  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r""")
        for q,w,r in product(range(6),range(2),range(2)):
            code.append(f"  · exact {name}_k{12*w+6*r+q:02}_checked")
    def descend(n,p,name):
        if n.size<=shardlimit:
            mod=f"Raw110Shard_{name}"
            code=[]
            local(n,p,name,code)
            emit(mod,imports,code)
            return mod
        # Recursively emit child modules; parent only checks first-hole split.
        n0,s0=n.head.removeprefix(".split ").split(" ",1)
        child_names=[]; child_mods=[]
        for j,k in enumerate(n.children):
            kname=f"{name}_k{j:02}"
            child_mods.append(descend(k,f"(refine {p} {s0} (some {move(MOVES[j])}))",kname))
            child_names.append(kname if not n.open_count or k.open_count else f"(.closed {kname})")
        partial=n.open_count!=0
        ty="PartialAudit" if partial else "Audit"
        checker="partialCheck" if partial else "zipCheck"
        bymove="byPartialMove" if partial else "byMove"
        kidexpr=f"({bymove} ["+",".join(child_names)+"])"
        code=[f"def {name} : {ty} := {n.head} {kidexpr}",f"theorem {name}_checked : {checker} {B} {p} {name} = true := by",
        f"  change (zipQueryOK {B} {p} {n0} {s0} && allMoves (fun mv => {checker} {B} (refine {p} {s0} (some mv)) ({kidexpr} mv))) = true",
        """  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r"""]
        for q,w,r in product(range(6),range(2),range(2)):
            code.append(f"  · exact {name}_k{12*w+6*r+q:02}_checked")
        mod=f"Raw110Shard_{name}"
        emit(mod,child_mods,code)
        return mod
    return descend(node,p,rootname)

selected=set(map(int,spec))
if len(sys.argv)>1:
    selected=set(map(int,sys.argv[1:]))
    assert selected<=set(map(int,spec))
with tempfile.TemporaryDirectory() as d:
    tmp=Path(d)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(tmp/"enumerate")],check=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent1-ngram/ngram.cpp"),"-o",str(tmp/"ngram")],check=True)
    for i in sorted(selected):
        s=spec[str(i)]
        p=PARENT[:5]+(MOVES[i],)+PARENT[6:]
        subprocess.run([str(tmp/"enumerate"),one.show(p)],cwd=tmp,check=True)
        data=(tmp/"open.txt").read_bytes()
        assert hashlib.sha256(data).hexdigest()==s["sha256"]
        opens=data.decode().splitlines()
        assert len(opens)==s["len"]==len(set(opens))
        index={t:j for j,t in enumerate(opens)}
        ns=f"BB6.Agent7Raw110PartialPumps{i:02}"
        pc=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
            f"namespace {ns}","open BB6Coverage BB6Coverage.Agent31Pump"]
        proofs={}
        for key,mod in [("one",one),("two",multi)]:
            for j in s[key]:
                p0=one.parse(opens[j]);ans=mod.candidate(p0,one.concrete_events(p0,6000))
                assert ans is not None,(i,j,key)
                code,info=mod.generate(j,p0,ans);pc.append(code)
                proofs[j]=(f"{ns}.M{j}.table",f"{ns}.M{j}.never")
        pc.append(f"end {ns}")
        pumpname=f"Raw110PartialPump{i:02}"
        (ROOT/(pumpname+".lean")).write_text("\n\n".join(pc)+"\n")
        ngname=f"Raw110NGram{i:02}"
        ngns=f"BB6.Agent7Raw110NGram{i:02}"
        ngcode=["import NGramCertificate","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {ngns}","open BB6Coverage BB6.Agent1NGram"]
        for j,k in s["ng"].items():
            j=int(j)
            c=subprocess.run([str(tmp/"ngram"),str(k)],input=f"{j} {opens[j]}\n",text=True,capture_output=True,check=True)
            idx,cert=c.stdout.strip().split(maxsplit=1)
            assert int(idx)==j and int(cert.split()[0])<=k
            ngcode.append(emit_ngram.emit(j,opens[j],cert))
            proofs[j]=(f"{ngns}.p{j}",f"{ngns}.never{j}")
        ngcode.append(f"end {ngns}")
        (ROOT/(ngname+".lean")).write_text("\n".join(ngcode)+"\n")
        for j in s["counter"]:
            assert opens[j]=="1RB0LA_1RC1RF_0RD1LF_1LD1RE_---0LC_1LA0RF"
            proofs[j]=("BB6.Agent7Raw110UnaryCounter.table","BB6.Agent7Raw110UnaryCounter.never")
        stats=Counter(); remaining=[]
        bank=[(int(a[0]),[int(c,36) for c in a[1:]]) for a in s["bank"]]
        def build(node):
            tag,*v=node
            stats[tag]+=1
            if tag=="cycle":
                e,k,r,b=v
                return Node(f".cycle {e} {k} {str(r).lower()} ({b})")
            if tag=="last":
                n,s0=v
                return Node(f".last {n} {slot(s0)}")
            if tag=="open":
                j=index[v[0]]
                if j in s["miss"]:
                    assert v[0].count("---")==1
                    remaining.append(v[0])
                    return Node(".unresolved",open_count=1)
                if j in proofs:
                    a,b=proofs[j]
                    return Node(f".proven {a} {b}")
                if str(j) in s["late"]:
                    n,s0=s["late"][str(j)]
                    return Node(f".last {n} {slot(s0)}")
                for rev,dfa in bank:
                    try:
                        n,D,L,R,z=masks(one.parse(v[0]),rev,dfa)
                    except AssertionError:
                        continue
                    return Node(f".far {str(bool(rev)).lower()} {n} ⟨0,{D},{L},{R},{z}⟩")
                raise ValueError(("bank failed",i,j,v[0]))
            assert tag=="split"
            n,s0,kids=v
            assert len(kids)==24
            cs=[build(k) for k in kids]
            return Node(f".split {n} {slot(s0)}",cs,1+sum(k.size for k in cs),sum(k.open_count for k in cs))
        tree=build(json.loads((tmp/"tree.json").read_text()))
        assert stats["open"]==len(opens)
        assert tree.open_count==len(s["miss"])==len(remaining)
        pexpr=f"(child110 {move(MOVES[i])})"
        name=f"partialKid{i:02}"
        mod=build_module(tree,pexpr,name,["Raw110Base",pumpname,ngname,"Raw110UnaryCounter"])
        emit(f"Raw110Partial{i:02}",[mod],[f"theorem countPartial{i:02} : (partialResiduals {pexpr} {name}).length = {tree.open_count} := by decide",
             f"#print axioms {name}_checked",f"#print axioms countPartial{i:02}"])
        (ROOT/f"remaining{i:02}.txt").write_text("\n".join(remaining)+"\n")
        print(i,stats,"retained",tree.open_count,"nodes",tree.size,flush=True)
