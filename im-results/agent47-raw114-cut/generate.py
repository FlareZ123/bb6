"""Generate proof data for raw114's two-level cut. Unresolved leaves stay open."""
from pathlib import Path
from itertools import product
from collections import Counter
import json, subprocess, tempfile

ROOT=Path(__file__).resolve().parent
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
def move(a):
    return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"
def slot(s):
    return f"({s//2},{str(bool(s%2)).lower()})"
with tempfile.TemporaryDirectory() as d:
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT/"enumerate_cut.cpp"),"-o",d+"/enumerate"],check=True)
    subprocess.run([d+"/enumerate"],cwd=d,check=True)
    tree=json.loads((Path(d)/"cut.json").read_text())

HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw114
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+HEADER+body+"\nend BB6.Agent47Raw114\n")
stats=Counter()
def full(node):
    tag,*v=node
    stats["full_"+tag]+=1
    if tag=="cycle":
        e,k,r,b=v
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v
        return f".last {n} {slot(s)}"
    assert tag=="split",node
    n,s,kids=v
    assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(full(k) for k in kids)+"])"
def partial(node):
    tag,*v=node
    stats[tag]+=1
    if tag=="unresolved": return ".unresolved"
    if tag=="closed": return ".closed ("+full(v[0])+")"
    assert tag=="split",node
    n,s,kids=v
    assert len(kids)==24
    return f".split {n} {slot(s)} (byPartialMove [\n"+",\n".join(partial(k) for k in kids)+"])"
assert tree[:3]==["split",8,8]
emit("Raw114CutBase",["PartialAudit"],"""
abbrev raw114 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,3⟩)
theorem raw114_root : raw114 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem raw114_nohalt : weightedTNFNoAssignedHalt raw114 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev raw114Child (mv : Move) := refine raw114 (4,false) (some mv)
theorem raw114Query : zipQueryOK 39 raw114 8 (4,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw114CutKid{i:02}";mods.append(name)
    emit(name,["Raw114CutBase"],f"""
def kid{i:02} : PartialAudit := {partial(kid)}
theorem check{i:02} : partialCheck 39 (raw114Child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=16,closed=209,unresolved=183,full_cycle=2871,full_last=420,full_split=134),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
emit("Raw114CutData",mods,"""
def kids : Move → PartialAudit := byPartialMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids_checked (mv : Move) : partialCheck 39 (raw114Child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def cutTree : PartialAudit := .split 8 (4,false) kids
theorem cut_checked : partialCheck 39 raw114 cutTree = true := by
  change (zipQueryOK 39 raw114 8 (4,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 39 (raw114Child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨raw114Query, allMoves_of _ kids_checked⟩
def raw114Residuals : List (List Move × PartialMachine) := partialResiduals raw114 cutTree
theorem raw114Residuals_count : raw114Residuals.length = 183 := by decide
theorem raw114Cut_sound :
    ∀ m, compatible raw114 m → WeightedBound 39 m ∨
      ∃ e ∈ raw114Residuals, compatible e.2 m :=
  partialSound 39 raw114 cutTree raw114_root raw114_nohalt cut_checked
#print axioms cut_checked
#print axioms raw114Residuals_count
#print axioms raw114Cut_sound
""")
print("candidate tree stats:",stats)
