"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1LF"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="9f7ea936ec2710ed5d4909338c31a74e0c5f0a71574e69d1f9d88b4f5dd62f17"
opens=raw.decode().splitlines()
assert len(opens)==126 and len(set(opens))==126
index={s:i for i,s in enumerate(opens)}
dfa=["00102030400"]*len(opens)
for row in (ROOT/"dfa.txt").read_text().split():
    a,indices=row.split(":")
    for i in indices.split(","):
        dfa[int(i)]=a
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw104
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent8Raw104\n"
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
assert tree[:3]==["split",9,10]
emit("Raw104Base",["ThreeHoleAudit"],"""
abbrev p104 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨true,false,5⟩)
theorem p104_root : p104 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p104_nohalt : weightedTNFNoAssignedHalt p104 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child104 (mv : Move) := refine p104 (5,false) (some mv)
theorem query104 : queryOK 78 p104 9 (5,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw104Kid{i:02}";mods.append(name)
    emit(name,["Raw104Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 78 (child104 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=115,cycle=1965,last=578,open=126),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids104 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids104_checked (mv : Move) : check 78 (child104 mv) (kids104 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree104 : Audit := .split 9 (5,false) kids104
theorem tree104_checked : check 78 p104 tree104 = true := by
  change (queryOK 78 p104 9 (5,false) && allMoves (fun mv => check 78 (child104 mv) (kids104 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query104, allMoves_of _ kids104_checked⟩
noncomputable def certificate104 : WeightedTNFCertificate 78 p104 6 :=
  certified 78 p104 tree104 p104_root p104_nohalt tree104_checked
theorem all104 : ∀ m, compatible p104 m → WeightedBound 78 m :=
  certificate104.sound

theorem attained104 : ∃ m, compatible p104 m ∧ HaltsAfter m 77 := by
  let p := child104 ⟨false,true,4⟩
  let p' := refine p (4,false) (some ⟨true,true,0⟩)
  let p'' := refine p' (0,true) (some ⟨false,true,1⟩)
  let m := weightedTNFDefaultCompletion (refine p'' (2,true) none)
  have h0 : p104 (5,false) = none := by decide
  have h1 : p (4,false) = none := by decide
  have h2 : p' (0,true) = none := by decide
  have h3 : p'' (2,true) = none := by decide
  have hr : (knownRun p'' 77).map readSlot = some (2,true) := by decide
  have hm : compatible (refine p'' (2,true) none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hp'' : compatible p'' m := refine_preserves_compat p'' m (2,true) none h3 hm
  have hp' : compatible p' m := refine_preserves_compat p' m (0,true) (some ⟨false,true,1⟩) h2 hp''
  have hp : compatible p m := refine_preserves_compat p m (4,false) (some ⟨true,true,0⟩) h1 hp'
  have hpar : compatible p104 m := refine_preserves_compat p104 m (5,false) (some ⟨false,true,4⟩) h0 hp
  refine ⟨m,hpar,?_⟩
  cases hrun : knownRun p'' 77 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (2,true) := by simpa [hrun] using hr
    apply first_hole_halts p'' 77 c hrun
    · simpa [hs] using h3
    · simpa [hs] using hm

theorem exact104 (B : Nat) :
    (∀ m, compatible p104 m → WeightedBound B m) ↔ 78 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained104
    have hz := firstOne_terminal p104 p104_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 77 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all104 m hm k d hk hd) hb

#print axioms tree104_checked
#print axioms all104
#print axioms attained104
#print axioms exact104
"""
emit("Raw104Data",mods,body)
print("Candidate tree:",stats,"FAR",len(opens))
