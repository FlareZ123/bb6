"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RF"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="c1fc92cbf77c8390ef9cbd63342ac1ab88aed604207fa054a6af4bc008f95910"
opens=raw.decode().splitlines()
assert len(opens)==47 and len(set(opens))==47
index={s:i for i,s in enumerate(opens)}
dfa=["00102030400"]*len(opens)
for row in (ROOT/"dfa.txt").read_text().split():
    i,a=row.split(":")
    dfa[int(i)]=a
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw103
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent3Raw103\n"
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
emit("Raw103Base",["ThreeHoleAudit"],"""
abbrev p103 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,5⟩)
theorem p103_root : p103 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p103_nohalt : weightedTNFNoAssignedHalt p103 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child103 (mv : Move) := refine p103 (5,false) (some mv)
theorem query103 : queryOK 116 p103 10 (5,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw103Kid{i:02}";mods.append(name)
    emit(name,["Raw103Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 116 (child103 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=81,cycle=1592,last=248,open=47),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids103 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids103_checked (mv : Move) : check 116 (child103 mv) (kids103 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree103 : Audit := .split 10 (5,false) kids103
theorem tree103_checked : check 116 p103 tree103 = true := by
  change (queryOK 116 p103 10 (5,false) && allMoves (fun mv => check 116 (child103 mv) (kids103 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query103, allMoves_of _ kids103_checked⟩
noncomputable def certificate103 : WeightedTNFCertificate 116 p103 6 :=
  certified 116 p103 tree103 p103_root p103_nohalt tree103_checked
theorem all103 : ∀ m, compatible p103 m → WeightedBound 116 m :=
  certificate103.sound

theorem attained103 : ∃ m, compatible p103 m ∧ HaltsAfter m 115 := by
  let p := child103 ⟨false,false,1⟩
  let p' := refine p (4,false) (some ⟨false,true,2⟩)
  let p'' := refine p' (2,true) (some ⟨false,false,0⟩)
  let m := weightedTNFDefaultCompletion (refine p'' (0,true) none)
  have h0 : p103 (5,false) = none := by decide
  have h1 : p (4,false) = none := by decide
  have h2 : p' (2,true) = none := by decide
  have h3 : p'' (0,true) = none := by decide
  have hr : (knownRun p'' 115).map readSlot = some (0,true) := by decide
  have hm : compatible (refine p'' (0,true) none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hp'' : compatible p'' m := refine_preserves_compat p'' m (0,true) none h3 hm
  have hp' : compatible p' m := refine_preserves_compat p' m (2,true) (some ⟨false,false,0⟩) h2 hp''
  have hp : compatible p m := refine_preserves_compat p m (4,false) (some ⟨false,true,2⟩) h1 hp'
  have hpar : compatible p103 m := refine_preserves_compat p103 m (5,false) (some ⟨false,false,1⟩) h0 hp
  refine ⟨m,hpar,?_⟩
  cases hrun : knownRun p'' 115 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [hrun] using hr
    apply first_hole_halts p'' 115 c hrun
    · simpa [hs] using h3
    · simpa [hs] using hm

theorem exact103 (B : Nat) :
    (∀ m, compatible p103 m → WeightedBound B m) ↔ 116 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := attained103
    have hz := firstOne_terminal p103 p103_root m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 115 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all103 m hm k d hk hd) hb

#print axioms tree103_checked
#print axioms all103
#print axioms attained103
#print axioms exact103
"""
emit("Raw103Data",mods,body)
print("Candidate tree:",stats,"FAR",len(opens))
