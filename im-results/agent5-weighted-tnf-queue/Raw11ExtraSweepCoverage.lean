import Root56Coverage
import Raw11ExtraNever
namespace Raw11ExtraSweepCoverage
open BB6Coverage BB6.Agent13BlankDelay
open Root56Coverage (center center_right center_left center_blank)

def table (v : Bool) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨v,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some (if v then ⟨false,false,4⟩ else ⟨false,true,0⟩))
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some (if v then ⟨false,true,0⟩ else ⟨true,false,0⟩))
  | _,_ => none

theorem step_center {v : Bool} {m : Machine} (hm : compatible (table v) m) (c : Config) (r : Root56.Config)
    (h : Raw11ExtraSweep.step v (center c) = some r) :
    ∃ s, rawStep m c = some s ∧ center s = r := by
  have hq : c.state.val = 0 ∨ c.state.val = 1 ∨ c.state.val = 2 ∨ c.state.val = 3 ∨ c.state.val = 4 ∨ c.state.val = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> cases hb : c.tape c.head <;> cases v <;>
    simp [center,Root56.c,Raw11ExtraSweep.step,hq,hb] at h
  all_goals
    have ht := hm (readSlot c) _ (by simp only [table,hq,hb]; rfl)
    simp only [rawStep,ht,Bool.false_eq_true,ite_false,ite_true]
    exact ⟨_,rfl,by first | rw [center_right]; exact h | rw [center_left]; exact h⟩

theorem run_center {v : Bool} {m : Machine} (hm : compatible (table v) m) (n : Nat) (c : Config) (r : Root56.Config)
    (h : Raw11ExtraSweep.run v n (center c) = some r) :
    ∃ s, run m n c = some s ∧ center s = r := by
  induction n generalizing r with
  | zero => exact ⟨c,rfl,Option.some.inj h⟩
  | succ n ih =>
    rw [Raw11ExtraSweep.run_add] at h
    cases hr : Raw11ExtraSweep.run v n (center c) with
    | none => simp [hr] at h
    | some r' =>
      obtain ⟨s,hs,hc⟩ := ih r' hr
      have hstep : Raw11ExtraSweep.step v (center s) = some r := by
        rw [hc]
        simpa [hr,Raw11ExtraSweep.run] using h
      obtain ⟨s',hs',hc'⟩ := step_center hm s r hstep
      exact ⟨s',by rw [run.eq_2,hs]; exact hs',hc'⟩

theorem never_compatible {v : Bool} (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  have hn := Raw11ExtraSweep.never v n
  rw [← center_blank] at hn
  cases h : Raw11ExtraSweep.run v n (center blank) with
  | none => exact False.elim (hn h)
  | some r =>
    obtain ⟨s,hs,_⟩ := run_center hm n blank r h
    rw [hs]; rfl

theorem weighted (v : Bool) (B : Nat) : Cover (WeightedBound B) (table v) :=
  .leaf _ fun m hm => weighted_never B m (never_compatible m hm)

#print axioms never_compatible
#print axioms weighted
end Raw11ExtraSweepCoverage
