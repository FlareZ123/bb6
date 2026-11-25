#!/usr/bin/env python3
"""Deterministic Raw39 A1=1RB witness regeneration. The Lean checker, not this
program, establishes coverage. Existing Raw121 producer and SweepPumping are
reused verbatim. The parent audit explicitly retains all other open children.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "_build1RB"
SOURCE = ROOT.parent / "agent11-raw121"
MULTI = ROOT.parent / "agent10-tnf-multipump"
THREE = ROOT.parent / "agent31-three-hole-tnf"
sys.path[:0] = [str(MULTI), str(THREE)]
import multi as m
from generate_sweeps import parse
from generate_four_hole import masks, slot, move
from chunk_checks import partition

PARENT = "1RB---_1RC---_0RD---_1LD0RA_------_------"
CHILD = "1RB1RB_1RC---_0RD---_1LD0RA_------_------"
BOUND = 175
OPEN_SHA = "5a99ae8878a6c8b3b12c75f7fa1ed3c7b298fac46fa7a13f776d154bf1982cb1"
STATS = dict(cycle=164550, last=44788, open=2654, split=9217)
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
COUNTERS = {
    2391:"1RB1RB1RC1RE0RD1RB1LD0RA1LF---1LC0LF",
    2575:"1RB1RB1RC1RF0RD1RB1LD0RA1LC0LE1LE---",
}
DATA = json.loads((ROOT/"witnesses.json").read_text())

PUMP_HEADER = """import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Pumps
open BB6Coverage BB6Coverage.Agent31Pump
"""
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""
FOOTER = "\nend BB6.Agent11Raw39\n"

def emit(name, imports, body):
    (ROOT/(name+".lean")).write_text(
        "".join(f"import {x}\n" for x in imports)+HEADER+body+FOOTER)

def run(*args, **kw):
    return subprocess.run([str(a) for a in args], check=True, **kw)

def counts(tree):
    c=Counter()
    def rec(t):
        c[t[0]]+=1
        if t[0]=="split":
            assert len(t[3])==24
            for x in t[3]:rec(x)
    rec(tree)
    return dict(c)

def generate_pumps(opens):
    modules={}
    chunks=[]
    specs=DATA["specs"]
    assert len(specs)==78
    for start in range(0,len(specs),10):
        name=f"Raw39Pumps{start//10:02}"
        out=[PUMP_HEADER]
        for i,t,side,q,a,b,ss in specs[start:start+10]:
            i,t,q,a,b=map(int,(i,t,q,a,b))
            assert i not in modules
            p=parse(opens[i])
            w=m.clean(tuple((v.lstrip("*"),v.startswith("*")) for v in ss.split(",")))
            v=m.clean(tuple(x for word,rep in w for x in
                            (((word,False),(word,True)) if rep else ((word,False),))))
            st=m.C(q,w if side=="R" else (),w if side=="L" else ())
            tg=m.C(q,v if side=="R" else (),v if side=="L" else ())
            ans=m.pump(p,st,tg,500)
            assert ans is not None,i
            code,info=m.generate(i,p,(t,st,tg,ans))
            assert info==(t,a,b),(i,info,(t,a,b))
            out.append(code)
            ns=f"BB6.Agent11Raw39Pumps.M{i}"
            modules[i]=(ns+".table",ns+".never")
        out.append("end BB6.Agent11Raw39Pumps")
        (ROOT/(name+".lean")).write_text("\n\n".join(out)+"\n")
        chunks.append(name)
    oldword=m.word
    for i,table in COUNTERS.items():
        assert opens[i].replace("_","")==table
        p=parse(table)
        L=m.lit("011111")+m.rep("1111")+m.lit("00")
        cases=[("Init",(),m.lit("1010")+m.rep("0000")+m.lit("101")),
               ("Carry",m.lit("0000")+m.rep("X"),
                m.lit("1010")+m.rep("0000")+m.lit("1010")+m.rep("X"))]
        name=f"Raw39Counter{i}"
        ns=f"BB6.Agent11Raw39Counter{i}"
        out=[PUMP_HEADER.replace("BB6.Agent11Raw39Pumps",ns)]
        # X denotes an arbitrary untouched List Bool, not an n-fold word.
        m.word=lambda w,n="n":m.app(*[
            "R" if s=="X" else f"rep {m.bits(s)} ({n})" if b else m.bits(s)
            for s,b in w])
        for section,a,b in cases:
            st=m.C(1,L,a)
            tg=m.C(1,m.lit("0100"),b)
            ans=m.pump(p,st,tg,300)
            assert ans is not None,(i,section)
            code,info=m.generate(i,p,(0,st,tg,ans),epoch=True)
            assert info==(0,44,4)
            code=code.replace(f"namespace M{i}",f"namespace {section}").replace(f"end M{i}",f"end {section}")
            if section=="Carry":
                code=code.replace("(n : Nat)","(n : Nat) (R : List Bool)")
                code=re.sub(r"(phase\d+|final[LR]) n\b",r"\1 n R",code)
            out.append(code)
        m.word=oldword
        out.extend([DATA["counter_tail"],"end "+ns])
        (ROOT/(name+".lean")).write_text("\n\n".join(out)+"\n")
        chunks.append(name)
        modules[i]=(ns+".Init.table",ns+".never")
    assert len(modules)==80
    return modules,chunks

def generate():
    BUILD.mkdir(exist_ok=True)
    run("g++","-std=c++17","-O3",SOURCE/"fast_enum.cpp","-o",BUILD/"enum")
    res=run(BUILD/"enum",CHILD,cwd=BUILD,text=True,capture_output=True)
    print(res.stdout,flush=True)
    assert re.search(r"maxscore=175\b",res.stdout)
    tree=json.loads((BUILD/"tree.json").read_text())
    opens=(BUILD/"open.txt").read_text().splitlines()
    assert hashlib.sha256((BUILD/"open.txt").read_bytes()).hexdigest()==OPEN_SHA
    assert len(opens)==len(set(opens))==2654
    assert counts(tree)==STATS and tree[:3]==["split",7,3]
    index={s:i for i,s in enumerate(opens)}
    special,chunks=generate_pumps(opens)
    # Validate masks even if the fast bank producer would accept. The actual
    # Lean FAR checker independently verifies the emitted masks.
    bank=DATA["bank"]
    assert len(bank)==len(set(bank))==55
    run("g++","-std=c++20","-O3",SOURCE/"bank.cpp","-o",BUILD/"bank")
    (BUILD/"bank.txt").write_text("\n".join(bank)+"\n")
    text="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens) if i not in special)
    res=run(BUILD/"bank",BUILD/"bank.txt",input=text,text=True,capture_output=True)
    assert not res.stderr.strip(),res.stderr
    found={int(i):a for i,a in (line.split() for line in res.stdout.splitlines())}
    assert set(found)==set(range(len(opens)))-set(special)
    far={}
    for i,a in found.items():
        for c in [a]+[c for c in bank if c!=a]:
            try:
                d,D,L,R,z=masks(parse(opens[i]),int(c[0]),[int(ch,36) for ch in c[1:]])
                far[i]=f".far {str(bool(int(c[0]))).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
                break
            except (AssertionError,IndexError,ValueError):
                continue
        else:raise AssertionError((i,opens[i]))
    assert len(far)==2574
    def build(node):
        tag,*v=node
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,s=v
            return f".last {n} {slot(s)}"
        if tag=="open":
            i=index[v[0]]
            if i in special:
                p,h=special[i]
                return f".proven ({p}) (fun m hm => {h} m hm)"
            return far[i]
        assert tag=="split"
        n,s,kids=v
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(build,kids))+"])"

    emit("Raw39Base",["ZipThreeHoleAudit"]+chunks,r"""
abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev p1RB : PartialMachine := refine p39 (0,true) (some ⟨true,true,1⟩)
theorem p1RB_root : p1RB initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p1RB_nohalt : weightedTNFNoAssignedHalt p1RB :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev child39 (mv : Move) := refine p1RB (1,true) (some mv)
theorem query1RB : zipQueryOK 175 p1RB 7 (1,true) = true := by decide
theorem query39 : zipQueryOK 175 p39 6 (0,true) = true := by decide
""")
    kids=[]
    for i,k in enumerate(tree[3]):
        name=f"Raw39Kid{i:02}"
        kids.append(name)
        emit(name,["Raw39Base"],f"def kid{i:02} : Audit := {build(k)}\n\n"
             f"theorem check{i:02} : zipCheck {BOUND} (child39 {move(MOVES[i])}) kid{i:02} = true := by decide\n")
        p=ROOT/(name+".lean")
        content,n=partition(p.read_text(),180)
        p.write_text(content)
        print(name,"subproofs",n,flush=True)
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    names=",".join(f"kid{i:02}" for i in range(24))
    emit("Raw39Data",["Raw39Base"]+kids,f"""
def kids39 : Move → Audit := byMove [{names}]
theorem kids39_checked (mv : Move) : zipCheck 175 (child39 mv) (kids39 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree1RB : Audit := .split 7 (1,true) kids39
theorem tree1RB_checked : zipCheck 175 p1RB tree1RB = true := by
  change (zipQueryOK 175 p1RB 7 (1,true) && allMoves (fun mv => zipCheck 175 (child39 mv) (kids39 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query1RB,allMoves_of _ kids39_checked⟩
noncomputable def certificate1RB : WeightedTNFCertificate 175 p1RB 6 :=
  certifiedZip 175 p1RB tree1RB p1RB_root p1RB_nohalt tree1RB_checked
theorem all1RB : ∀ m, compatible p1RB m → WeightedBound 175 m := certificate1RB.sound
#print axioms tree1RB_checked
#print axioms all1RB
""")
    # Raw39 root first-hole partition: ten closed nonhalting/nonhalt-bounded
    # ordinary children, the halt branch, and fourteen explicit open children.
    cycles={1:(0,10,True,0),2:(13,1,False,1),3:(10,1,False,0),
            6:(0,8,True,0),9:(0,8,True,0),14:(0,12,True,0),
            15:(10,1,False,0),18:(0,8,True,0),21:(0,8,True,0)}
    branches=[]
    for i in range(24):
        if i==19:branches.append(".closed tree1RB")
        elif i in cycles:
            e,k,r,b=cycles[i]
            branches.append(f".closed (.cycle {e} {k} {str(r).lower()} ({b}))")
        else:branches.append(".unresolved")
    pcs="\n".join("  · exact tree1RB_checked" if 12*w+6*r+q==19 else "  · decide"
                  for q,w,r in product(range(6),range(2),range(2)))
    branch_text=",\n  ".join(branches)
    emit("Raw39Partial",["Raw39Data","PartialAudit"],f"""
open BB6.Agent47PartialAudit
def partialKids : Move → PartialAudit := byPartialMove [
  {branch_text}]
def partialTree : PartialAudit := .split 6 (0,true) partialKids
theorem partialKids_checked (mv : Move) :
    partialCheck 175 (refine p39 (0,true) (some mv)) (partialKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{pcs}
theorem partialTree_checked : partialCheck 175 p39 partialTree = true := by
  change (zipQueryOK 175 p39 6 (0,true) && allMoves (fun mv => partialCheck 175 (refine p39 (0,true) (some mv)) (partialKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query39,allMoves_of _ partialKids_checked⟩
def residuals := partialResiduals p39 partialTree
theorem residual_count : residuals.length = 14 := by decide
theorem cut_sound : ∀ m, compatible p39 m →
    WeightedBound 175 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 175 p39 partialTree p39_root p39_nohalt partialTree_checked
#print axioms cut_sound
#print axioms residual_count
""")
    manifest=dict(parent=PARENT,child=CHILD,bound=BOUND,open_sha256=OPEN_SHA,
                  stats=STATS,symbolic=80,far=2574,remaining_root_children=14,
                  tree_sha256=hashlib.sha256((BUILD/"tree.json").read_bytes()).hexdigest(),
                  proof_modules=chunks,child_modules=kids)
    (ROOT/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print("Raw39 1RB source candidate generated",manifest,flush=True)

if __name__=="__main__":
    generate()
