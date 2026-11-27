import PackedCycle
import FastThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48OneLAPacked
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6Coverage.Agent50SideCycle BB6.Agent3PackedCycle

def ctr : PartialMachine := fromCodes [7,20,11,7,14,1,24,16,2,11,8,4]

def lookup (q : Fin 6) (b : Bool) : Option Move :=
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,5⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,true,1⟩
  | 2,false => some ⟨true,false,3⟩
  | 2,true => some ⟨false,true,0⟩
  | 3,false => none
  | 3,true => some ⟨false,false,4⟩
  | 4,false => some ⟨true,false,0⟩
  | 4,true => some ⟨true,true,2⟩
  | 5,false => some ⟨false,false,2⟩
  | 5,true => some ⟨false,false,1⟩
  | _,_ => none

def tab : PartialMachine := fun s => (lookup s.1 s.2).map some

theorem same : ctr = tab := BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)

def stepFast (z : H) : Option H := (lookup z.p.q (z.p.l % 2 == 1)).map (fun mv => moveH mv z)

theorem stepFast_eq (z : H) : stepH ctr z = stepFast z := by
  rw [same]
  unfold stepH stepFast readP tab
  cases lookup z.p.q (z.p.l % 2 == 1) <;> rfl

def checkSide (b : Bool) (h : Int) : Bool := if b then decide (996 ≤ h) else true

def runFast (b : Bool) : Nat → H → Option H
  | 0,z => some z
  | n+1,z => if checkSide b z.h then (stepFast z).bind (runFast b n) else none

theorem runFast_run (n : Nat) (z : H) : runFast false n z = runH ctr n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [runFast,runH,checkSide,Bool.false_eq_true,ite_false,ite_true,stepFast_eq]
    cases h : stepFast z with
    | none => rfl
    | some u => exact ih u

theorem runFast_window (n : Nat) (z : H) : runFast true n z = windowH ctr true 996 n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [runFast,windowH,checkSide,ite_true,stepFast_eq,side,decide_eq_true_eq]
    split
    · cases h : stepFast z with
      | none => rfl
      | some u => exact ih u
    · rfl

theorem runFast_join {b : Bool} {n k : Nat} {a c d : H}
    (h : runFast b n a = some c) (g : runFast b k c = some d) :
    runFast b (n+k) a = some d := by
  induction n generalizing a with
  | zero => have e : a = c := Option.some.inj h; subst a; simpa only [Nat.zero_add] using g
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [runFast] at h ⊢
    split at h
    · rename_i hb
      rw [if_pos hb]
      cases hs : stepFast a with
      | none => simp [hs] at h
      | some u => exact ih (by simpa [hs] using h)
    · contradiction

theorem mkCycle {a c : H} {e n : Nat} (he : runFast false e startH = some a)
    (hl : runFast true n a = some c) (ht : tailH true 996 a c = true) :
    cycleH ctr e n true 996 = true := by
  rw [runFast_run] at he
  rw [runFast_window] at hl
  simp only [cycleH,he,hl,ht]

#print axioms same
#print axioms runFast_run
#print axioms runFast_window
#print axioms runFast_join
#print axioms mkCycle
end BB6.Agent48OneLAPacked
