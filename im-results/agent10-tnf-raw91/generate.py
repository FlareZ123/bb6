"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RC"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="7a1658edbbcb3bbc12ec56e784d72ee90d8267d7ddf3bf57f5f31ce6a77b4783"
opens=raw.decode().splitlines()
assert len(opens)==72 and len(set(opens))==72
index={s:i for i,s in enumerate(opens)}
dfa=["00102030400"]*len(opens)
for row in (ROOT/"dfa.txt").read_text().split():
    i,a=row.split(":")
    dfa[int(i)]=a
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw91
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent10Raw91\n"
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
        if i==14:
            assert code=="1RB1RF_1RC1LF_0RD0LB_1LD1RE_---0LB_1RA0RC"
            return ".proven BB6.Agent10Raw91Pump.table BB6.Agent10Raw91Pump.never"
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",9,5]
emit("Raw91Base",["ThreeHoleAudit","Raw91Pump"],"""
abbrev p91 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,2⟩)
theorem p91_root : p91 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p91_nohalt : weightedTNFNoAssignedHalt p91 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child91 (mv : Move) := refine p91 (2,true) (some mv)
theorem query91 : queryOK 76 p91 9 (2,true) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw91Kid{i:02}";mods.append(name)
    emit(name,["Raw91Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 76 (child91 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=207,cycle=3838,last=875,open=72),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids91 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids91_checked (mv : Move) : check 76 (child91 mv) (kids91 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree91 : Audit := .split 9 (2,true) kids91
theorem tree91_checked : check 76 p91 tree91 = true := by
  change (queryOK 76 p91 9 (2,true) && allMoves (fun mv => check 76 (child91 mv) (kids91 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query91, allMoves_of _ kids91_checked⟩
noncomputable def certificate91 : WeightedTNFCertificate 76 p91 6 :=
  certified 76 p91 tree91 p91_root p91_nohalt tree91_checked
theorem all91 : ∀ m, compatible p91 m → WeightedBound 76 m :=
  certificate91.sound

theorem attained91 : ∃ m, compatible p91 m ∧ HaltsAfter m 75 := by
  let p := child91 ⟨true,true,3⟩
  let p' := refine p (4,false) (some ⟨false,false,5⟩)
  let p'' := refine p' (5,false) (some ⟨true,false,0⟩)
  let m := weightedTNFDefaultCompletion (refine p'' (0,true) none)
  have h0 : p91 (2,true) = none := by decide
  have h1 : p (4,false) = none := by decide
  have h2 : p' (5,false) = none := by decide
  have h3 : p'' (0,true) = none := by decide
  have hr : (knownRun p'' 75).map readSlot = some (0,true) := by decide
  have hm : compatible (refine p'' (0,true) none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hp'' : compatible p'' m := refine_preserves_compat p'' m (0,true) none h3 hm
  have hp' : compatible p' m := refine_preserves_compat p' m (5,false) (some ⟨true,false,0⟩) h2 hp''
  have hp : compatible p m := refine_preserves_compat p m (4,false) (some ⟨false,false,5⟩) h1 hp'
  have hpar : compatible p91 m := refine_preserves_compat p91 m (2,true) (some ⟨true,true,3⟩) h0 hp
  refine ⟨m,hpar,?_⟩
  cases hrun : knownRun p'' 75 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [hrun] using hr
    apply first_hole_halts p'' 75 c hrun
    · simpa [hs] using h3
    · simpa [hs] using hm

theorem exact91 (B : Nat) :
    (∀ m, compatible p91 m → WeightedBound B m) ↔ 76 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained91
    have hz := firstOne_terminal p91 p91_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 75 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all91 m hm k d hk hd) hb

#print axioms tree91_checked
#print axioms all91
#print axioms attained91
#print axioms exact91
"""
emit("Raw91Data",mods,body)
print("Candidate tree:",stats,"FAR",len(opens)-1,"symbolic pump",1)
