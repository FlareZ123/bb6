import WeightedTNF
import Root56

namespace Root56Coverage
open BB6Coverage
open BB6.Agent13BlankDelay

def nearL (c : Config) : Root56.Side := fun n => c.tape (c.head - ((n : Int) + 1))
def nearR (c : Config) : Root56.Side := fun n => c.tape (c.head + ((n : Int) + 1))
def center (c : Config) : Root56.Config := Root56.c c.state.val (nearL c) (c.tape c.head) (nearR c)

private theorem rightL (c : Config) (w : Bool) (q : Fin 6) :
    nearL (applyMove c ⟨w,true,q⟩) = Root56.push w (nearL c) := by
  funext n
  cases n with
  | zero => simp [nearL, applyMove, Root56.push]
  | succ n =>
    simp only [nearL,applyMove,ite_true,Root56.push]
    have h : c.head + 1 - (((n+1 : Nat) : Int) + 1) ≠ c.head := by omega
    rw [ite_eq_right h]
    congr 1 <;> omega

private theorem rightR (c : Config) (w : Bool) (q : Fin 6) :
    nearR (applyMove c ⟨w,true,q⟩) = Root56.tl (nearR c) := by
  funext n
  simp only [nearR,applyMove,ite_true,Root56.tl]
  have h : c.head + 1 + ((n : Int) + 1) ≠ c.head := by omega
  rw [ite_eq_right h]
  congr 1 <;> omega

private theorem leftL (c : Config) (w : Bool) (q : Fin 6) :
    nearL (applyMove c ⟨w,false,q⟩) = Root56.tl (nearL c) := by
  funext n
  simp only [nearL,applyMove,Bool.false_eq_true,ite_false,Root56.tl]
  have h : c.head + -1 - ((n : Int) + 1) ≠ c.head := by omega
  rw [ite_eq_right h]
  congr 1 <;> omega

private theorem leftR (c : Config) (w : Bool) (q : Fin 6) :
    nearR (applyMove c ⟨w,false,q⟩) = Root56.push w (nearR c) := by
  funext n
  cases n with
  | zero => simp [nearR,applyMove,Root56.push,show c.head + -1 + 1 = c.head by omega]
  | succ n =>
    simp only [nearR,applyMove,Bool.false_eq_true,ite_false,Root56.push]
    have h : c.head + -1 + (((n+1 : Nat) : Int) + 1) ≠ c.head := by omega
    rw [ite_eq_right h]
    congr 1 <;> omega

private theorem rightHead (c : Config) (w : Bool) (q : Fin 6) :
    (applyMove c ⟨w,true,q⟩).tape (applyMove c ⟨w,true,q⟩).head = Root56.hd (nearR c) := by
  simp [applyMove,Root56.hd,nearR,show c.head + 1 ≠ c.head by omega]

private theorem leftHead (c : Config) (w : Bool) (q : Fin 6) :
    (applyMove c ⟨w,false,q⟩).tape (applyMove c ⟨w,false,q⟩).head = Root56.hd (nearL c) := by
  simp [applyMove,Root56.hd,nearL,Int.sub_eq_add_neg,show c.head + -1 ≠ c.head by omega]

theorem center_right (c : Config) (w : Bool) (q : Fin 6) :
    center (applyMove c ⟨w,true,q⟩) = Root56.right q.val (nearL c) w (nearR c) := by
  simp only [center,Root56.right,rightL,rightR,rightHead]
  rfl

theorem center_left (c : Config) (w : Bool) (q : Fin 6) :
    center (applyMove c ⟨w,false,q⟩) = Root56.left q.val (nearL c) w (nearR c) := by
  simp only [center,Root56.left,leftL,leftR,leftHead]
  rfl

/-- The actual 11-entry cylinder, with F1 unspecified. -/
def table56 : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none

theorem step_center {m : Machine} (hm : compatible table56 m) (c : Config) (r : Root56.Config)
    (h : Root56.step (center c) = some r) :
    ∃ s, rawStep m c = some s ∧ center s = r := by
  have hq : c.state.val = 0 ∨ c.state.val = 1 ∨ c.state.val = 2 ∨ c.state.val = 3 ∨ c.state.val = 4 ∨ c.state.val = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> cases hb : c.tape c.head <;>
    simp [center,Root56.c,Root56.step,hq,hb] at h
  all_goals
    have ht := hm (readSlot c) _ (by simp only [table56,hq,hb]; rfl)
    simp only [rawStep,ht]
    exact ⟨_,rfl,by first | rw [center_right]; exact h | rw [center_left]; exact h⟩

theorem run_center {m : Machine} (hm : compatible table56 m) (n : Nat) (c : Config) (r : Root56.Config)
    (h : Root56.run n (center c) = some r) :
    ∃ s, run m n c = some s ∧ center s = r := by
  induction n generalizing r with
  | zero => exact ⟨c,rfl,Option.some.inj h⟩
  | succ n ih =>
    rw [Root56.run_add] at h
    cases hr : Root56.run n (center c) with
    | none => simp [hr] at h
    | some r' =>
      obtain ⟨s,hs,hc⟩ := ih r' hr
      have hstep : Root56.step (center s) = some r := by
        rw [hc]
        simpa [hr,Root56.run] using h
      obtain ⟨s',hs',hc'⟩ := step_center hm s r hstep
      exact ⟨s',by rw [run.eq_2,hs]; exact hs',hc'⟩

theorem center_blank : center blank = Root56.blank := rfl

theorem never_compatible (m : Machine) (hm : compatible table56 m) : NeverHalts m := by
  intro n
  have hn := Root56.never n
  rw [← center_blank] at hn
  cases h : Root56.run n (center blank) with
  | none => exact False.elim (hn h)
  | some r =>
    obtain ⟨s,hs,_⟩ := run_center hm n blank r h
    rw [hs]; rfl

theorem weighted (B : Nat) : Cover (WeightedBound B) table56 :=
  .leaf _ fun m hm => weighted_never B m (never_compatible m hm)

#print axioms never_compatible
#print axioms weighted
end Root56Coverage
