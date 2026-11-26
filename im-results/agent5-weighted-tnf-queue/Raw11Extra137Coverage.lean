import Root56Coverage
import Raw11Extra137
namespace Raw11Extra137Coverage
open BB6Coverage BB6.Agent13BlankDelay
open Root56Coverage (center center_right center_left center_blank)

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

theorem step_center {m : Machine} (hm : compatible table m) (c : Config) (r : Root56.Config)
    (h : Raw11Extra137.step (center c) = some r) :
    ∃ s, rawStep m c = some s ∧ center s = r := by
  have hq : c.state.val = 0 ∨ c.state.val = 1 ∨ c.state.val = 2 ∨ c.state.val = 3 ∨ c.state.val = 4 ∨ c.state.val = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> cases hb : c.tape c.head <;>
    simp [center,Root56.c,Raw11Extra137.step,hq,hb] at h
  all_goals
    have ht := hm (readSlot c) _ (by simp only [table,hq,hb]; rfl)
    simp only [rawStep,ht]
    exact ⟨_,rfl,by first | rw [center_right]; exact h | rw [center_left]; exact h⟩

theorem run_center {m : Machine} (hm : compatible table m) (n : Nat) (c : Config) (r : Root56.Config)
    (h : Raw11Extra137.run n (center c) = some r) :
    ∃ s, run m n c = some s ∧ center s = r := by
  induction n generalizing r with
  | zero => exact ⟨c,rfl,Option.some.inj h⟩
  | succ n ih =>
    rw [Raw11Extra137.run_add] at h
    cases hr : Raw11Extra137.run n (center c) with
    | none => simp [hr] at h
    | some r' =>
      obtain ⟨s,hs,hc⟩ := ih r' hr
      have hstep : Raw11Extra137.step (center s) = some r := by
        rw [hc]
        simpa [hr,Raw11Extra137.run] using h
      obtain ⟨s',hs',hc'⟩ := step_center hm s r hstep
      exact ⟨s',by rw [run.eq_2,hs]; exact hs',hc'⟩

theorem never_compatible (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  have hn := Raw11Extra137.never n
  rw [← center_blank] at hn
  cases h : Raw11Extra137.run n (center blank) with
  | none => exact False.elim (hn h)
  | some r =>
    obtain ⟨s,hs,_⟩ := run_center hm n blank r h
    rw [hs]; rfl

theorem weighted (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never_compatible m hm)

#print axioms never_compatible
#print axioms weighted
end Raw11Extra137Coverage
