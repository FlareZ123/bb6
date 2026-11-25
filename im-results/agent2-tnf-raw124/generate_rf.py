"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC---_0RD---_1LD1RE_---1LF_---0RF"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(ROOT/"enumerate")],check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="d3b2229b49131b93d467dec5a282832bfb8d3aebd62fc268939be8023fef84c0"
opens=raw.decode().splitlines()
assert len(opens)==42 and len(set(opens))==42
index={s:i for i,s in enumerate(opens)}
dfa=dict((int(i),v) for i,v in (line.split() for line in (ROOT/"rf-dfa.txt").read_text().splitlines()))
assert set(dfa)==set(range(42))
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124RF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent2Raw124RF\n"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+HEADER+body+FOOTER)
tree=json.loads((ROOT/"tree.json").read_text())
stats=Counter()
def build(node):
    tag,*v=node;stats[tag]+=1
    if tag=="cycle":
        e,k,r,b=v
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v;return f".last {n} {slot(s)}"
    if tag=="open":
        code=v[0];i=index[code];a=dfa[i]
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",10,10]
emit("Raw124RFBase",["ThreeHoleAudit"],"""
abbrev p124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev p0RF : PartialMachine :=
  refine p124 (5,true) (some ⟨false,true,5⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem p0RF_root : p0RF initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p0RF_nohalt : weightedTNFNoAssignedHalt p0RF :=
  weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt
abbrev child0RF (mv : Move) := refine p0RF (5,false) (some mv)
theorem query0RF : queryOK 71 p0RF 10 (5,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw124RFKid{i:02}";mods.append(name)
    emit(name,["Raw124RFBase"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 71 (child0RF {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=359,cycle=6979,last=1260,open=42),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids0RF : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids0RF_checked (mv : Move) : check 71 (child0RF mv) (kids0RF mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree0RF : Audit := .split 10 (5,false) kids0RF
theorem tree0RF_checked : check 71 p0RF tree0RF = true := by
  change (queryOK 71 p0RF 10 (5,false) && allMoves (fun mv => check 71 (child0RF mv) (kids0RF mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query0RF, allMoves_of _ kids0RF_checked⟩
noncomputable def certificate0RF : WeightedTNFCertificate 71 p0RF 6 :=
  certified 71 p0RF tree0RF p0RF_root p0RF_nohalt tree0RF_checked
theorem all0RF : ∀ m, compatible p0RF m → WeightedBound 71 m :=
  certificate0RF.sound

#print axioms tree0RF_checked
#print axioms all0RF
"""
emit("Raw124RFData",mods,body)
print("Candidate tree:",stats)
