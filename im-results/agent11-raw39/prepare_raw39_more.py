#!/usr/bin/env python3
"""Generate exact source-audit candidates for Raw39 0RB and 1RC."""
import hashlib
import json
import sys
from itertools import product
from pathlib import Path
import prepare_raw39 as common
import gen_auto_counters as counter
from gen_rc_counters import nextword

ROOT=Path(__file__).resolve().parent
BRANCH=sys.argv[1]
assert BRANCH in ("0RB","1RC")
PREFIX="Raw39B"+BRANCH
NS="BB6.Agent11"+PREFIX
BUILD=ROOT/("_build"+BRANCH)
DATA=json.loads((ROOT/"rb-rc-witnesses.json").read_text())[BRANCH]
BOUND=DATA["bound"]
CHILD="1RB"+BRANCH+"_1RC---_0RD---_1LD0RA_------_------"
SLOT=3 if BRANCH=="0RB" else 5
ROOTMOVE=7 if BRANCH=="0RB" else 20
m=common.m
parse=common.parse
masks=common.masks
slot=common.slot
move=common.move
MOVES=common.MOVES

HEADER=common.HEADER.replace("BB6.Agent11Raw39",NS)
FOOTER=common.FOOTER.replace("BB6.Agent11Raw39",NS)
PUMP_HEADER=common.PUMP_HEADER.replace("BB6.Agent11Raw39Pumps",NS+"Pumps")

def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join(f"import {x}\n" for x in imports)+HEADER+body+FOOTER)

def generate():
    BUILD.mkdir(exist_ok=True)
    common.run("g++","-std=c++17","-O3",common.SOURCE/"fast_enum.cpp","-o",BUILD/"enum")
    res=common.run(BUILD/"enum",CHILD,cwd=BUILD,text=True,capture_output=True)
    print(res.stdout,flush=True)
    tree=json.loads((BUILD/"tree.json").read_text())
    opens=(BUILD/"open.txt").read_text().splitlines()
    assert hashlib.sha256((BUILD/"open.txt").read_bytes()).hexdigest()==DATA["hash"]
    assert len(opens)==len(set(opens))==DATA["stats"]["open"]
    assert common.counts(tree)==DATA["stats"] and tree[:3]==["split",7,SLOT]
    index={s:i for i,s in enumerate(opens)}
    special,chunks=counter.generate(ROOT,opens,BRANCH,DATA["counters"])
    for start in range(0,len(DATA["specs"]),10):
        name=f"{PREFIX}Pumps{start//10:02}"
        out=[PUMP_HEADER]
        for i,t,side,q,a,b,ss in DATA["specs"][start:start+10]:
            i,t,q,a,b=map(int,(i,t,q,a,b));assert i not in special
            p=parse(opens[i])
            w=m.clean(tuple((v.lstrip("*"),v.startswith("*")) for v in ss.split(",")))
            v=nextword(w)
            st=m.C(q,w if side=="R" else (),w if side=="L" else ())
            tg=m.C(q,v if side=="R" else (),v if side=="L" else ())
            ans=m.pump(p,st,tg,2500);assert ans is not None,i
            code,info=m.generate(i,p,(t,st,tg,ans));assert info==(t,a,b),(i,info)
            out.append(code)
            ns=f"{NS}Pumps.M{i}"
            special[i]=(ns+".table",ns+".never")
        out.append("end "+NS+"Pumps")
        (ROOT/(name+".lean")).write_text("\n\n".join(out)+"\n")
        chunks.append(name)
    assert len(special)==len(DATA["specs"])+len(DATA["counters"])
    late={i:(n,s) for i,n,s in DATA["late"]}
    assert not set(late)&set(special) and len(late)==len(DATA["late"])
    bank=DATA["bank"];assert len(bank)==len(set(bank))
    common.run("g++","-std=c++20","-O3",common.SOURCE/"bank.cpp","-o",BUILD/"bank")
    (BUILD/"bank.txt").write_text("\n".join(bank)+"\n")
    todo=set(range(len(opens)))-set(special)-set(late)
    text="".join(f"{i} {opens[i].replace('_','')}\n" for i in sorted(todo))
    res=common.run(BUILD/"bank",BUILD/"bank.txt",input=text,text=True,capture_output=True)
    assert not res.stderr.strip(),res.stderr
    found={int(i):a for i,a in (line.split() for line in res.stdout.splitlines())}
    assert set(found)==todo
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
    assert set(far)==todo
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
            if i in late:
                n,s=late[i]
                return f".last {n} {slot(s)}"
            return far[i]
        assert tag=="split"
        n,s,kids=v
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(build,kids))+"])"

    emit(PREFIX+"Base",["ZipThreeHoleAudit"]+chunks,f"""
abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev pChild : PartialMachine := refine p39 (0,true) (some {move(MOVES[ROOTMOVE])})
theorem pChild_root : pChild initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pChild_nohalt : weightedTNFNoAssignedHalt pChild :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev child (mv : Move) := refine pChild ({SLOT//2},true) (some mv)
theorem queryChild : zipQueryOK {BOUND} pChild 7 ({SLOT//2},true) = true := by decide
theorem query39 : zipQueryOK {BOUND} p39 6 (0,true) = true := by decide
""")
    kids=[]
    for i,k in enumerate(tree[3]):
        name=f"{PREFIX}Kid{i:02}";kids.append(name)
        emit(name,[PREFIX+"Base"],f"def kid{i:02} : Audit := {build(k)}\n\n"
             f"theorem check{i:02} : zipCheck {BOUND} (child {move(MOVES[i])}) kid{i:02} = true := by decide\n")
        p=ROOT/(name+".lean")
        content,n=common.partition(p.read_text(),180);p.write_text(content)
        print(name,"subproofs",n,flush=True)
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    names=",".join(f"kid{i:02}" for i in range(24))
    emit(PREFIX+"Data",[PREFIX+"Base"]+kids,f"""
def kidsChild : Move → Audit := byMove [{names}]
theorem kidsChild_checked (mv : Move) : zipCheck {BOUND} (child mv) (kidsChild mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def treeChild : Audit := .split 7 ({SLOT//2},true) kidsChild
theorem treeChild_checked : zipCheck {BOUND} pChild treeChild = true := by
  change (zipQueryOK {BOUND} pChild 7 ({SLOT//2},true) && allMoves (fun mv => zipCheck {BOUND} (child mv) (kidsChild mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨queryChild,allMoves_of _ kidsChild_checked⟩
noncomputable def certificateChild : WeightedTNFCertificate {BOUND} pChild 6 :=
  certifiedZip {BOUND} pChild treeChild pChild_root pChild_nohalt treeChild_checked
theorem allChild : ∀ m, compatible pChild m → WeightedBound {BOUND} m := certificateChild.sound
#print axioms treeChild_checked
#print axioms allChild
""")
    cycles={1:(0,10,True,0),2:(13,1,False,1),3:(10,1,False,0),6:(0,8,True,0),9:(0,8,True,0),
            14:(0,12,True,0),15:(10,1,False,0),18:(0,8,True,0),21:(0,8,True,0)}
    branches=[]
    for i in range(24):
        if i==ROOTMOVE:branches.append(".closed treeChild")
        elif i in cycles:
            e,k,r,b=cycles[i]
            branches.append(f".closed (.cycle {e} {k} {str(r).lower()} ({b}))")
        else:branches.append(".unresolved")
    pcs="\n".join("  · exact treeChild_checked" if 12*w+6*r+q==ROOTMOVE else "  · decide"
                  for q,w,r in product(range(6),range(2),range(2)))
    branch_text=",\n  ".join(branches)
    emit(PREFIX+"Partial",[PREFIX+"Data","PartialAudit"],f"""
open BB6.Agent47PartialAudit
def partialKids : Move → PartialAudit := byPartialMove [
  {branch_text}]
def partialTree : PartialAudit := .split 6 (0,true) partialKids
theorem partialKids_checked (mv : Move) :
    partialCheck {BOUND} (refine p39 (0,true) (some mv)) (partialKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{pcs}
theorem partialTree_checked : partialCheck {BOUND} p39 partialTree = true := by
  change (zipQueryOK {BOUND} p39 6 (0,true) && allMoves (fun mv => partialCheck {BOUND} (refine p39 (0,true) (some mv)) (partialKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query39,allMoves_of _ partialKids_checked⟩
def residuals := partialResiduals p39 partialTree
theorem residual_count : residuals.length = 14 := by decide
theorem cut_sound : ∀ m, compatible p39 m →
    WeightedBound {BOUND} m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound {BOUND} p39 partialTree p39_root p39_nohalt partialTree_checked
#print axioms cut_sound
#print axioms residual_count
""")
    manifest=dict(parent=common.PARENT,child=CHILD,bound=BOUND,open_sha256=DATA["open_sha256"],
                  stats=DATA["stats"],symbolic=len(special),late=len(late),far=len(far),remaining_root_children=14,
                  tree_sha256=hashlib.sha256((BUILD/"tree.json").read_bytes()).hexdigest(),
                  proof_modules=chunks,child_modules=kids)
    (ROOT/("manifest-"+BRANCH+".json")).write_text(json.dumps(manifest,indent=2)+"\n")
    print("Raw39 "+BRANCH+" source candidate generated",manifest,flush=True)

if __name__=="__main__":
    generate()
