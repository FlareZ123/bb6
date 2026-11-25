"""Generate candidate audits for raw107 children with one- and two-block recurrences."""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
import multi

MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
SPECS=json.loads((ROOT/"specs_more.json").read_text())

def main(a):
    spec=SPECS[a]
    B=spec["bound"]
    n,s=spec["query"]
    PARENT=f"1RB---_1RC{a}_0RD---_1LD1RE_---0RB_------"
    pre=f"Raw107B{a}"
    ns=f"BB6.Agent11{pre}"
    target=ROOT/("generated_"+a);target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==spec["sha"]
    opens=data.decode().splitlines()
    assert len(opens)==spec["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*len(opens)
    for row in spec["groups"].splitlines():
        c,ids=row.split()
        for i in ids.split(","):dfa[int(i)]=c
    pn=ns+"Pumps"
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pn}","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for gen,inds,limit in [(one,spec["one"],1200),(multi,spec["multi"],2500)]:
        for i in inds:
            p=one.parse(opens[i]);ans=gen.candidate(p,one.concrete_events(p,limit))
            assert ans is not None,(a,i)
            code,info=gen.generate(i,p,ans)
            pumps[i]=f"{pn}.M{i}"
            pumpcode.append(code)
            print(a,i,info)
    manual=[]
    for i,(mod,nspace,table) in spec.get("manual",{}).items():
        assert opens[int(i)]==table,(a,i)
        pumps[int(i)]=nspace
        if mod not in manual:manual.append(mod)
    pumpcode.append(f"end {pn}")
    (ROOT/(pre+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
    def emit(name,imports,body):
        header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""
        (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+header+body+f"\nend {ns}\n")
    tree=json.loads((target/"tree.json").read_text());stats=Counter()
    def build(node):
        tag,*v=node;stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            nn,ss=v
            return f".last {nn} {slot(ss)}"
        if tag=="open":
            t=v[0];i=index[t]
            if i in pumps:return f".proven {pumps[i]}.table {pumps[i]}.never"
            c=dfa[i];rev=int(c[0]);d,D,L,R,z=masks(parse(t),rev,[int(ch,36) for ch in c[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        nn,ss,kids=v;assert len(kids)==24
        return f".split {nn} {slot(ss)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",n,s]
    bname=pre+"Base"
    emit(bname,["ZipThreeHoleAudit",pre+"Pumps"]+manual,f"""
abbrev p107 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,1⟩)
abbrev parent : PartialMachine := refine p107 (1,true) (some {move(a)})
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine parent {slot(s)} (some mv)
theorem query : zipQueryOK {B} parent {n} {slot(s)} = true := by decide
""")
    mods=[];stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"{pre}Kid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck {B} (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter(spec["stats"]),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    emit(pre+"Data",mods,f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck {B} (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split {n} {slot(s)} kids
theorem tree_checked : zipCheck {B} parent tree = true := by
  change (zipQueryOK {B} parent {n} {slot(s)} && allMoves (fun mv => zipCheck {B} (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedZip {B} parent tree parent_root parent_nohalt tree_checked
theorem all_completions : ∀ m, compatible parent m → WeightedBound {B} m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
""")
    print(stats,"FAR",len(opens)-len(pumps),"pumps",len(pumps))

if __name__=="__main__":
    for a in sys.argv[1:] or SPECS:main(a)
