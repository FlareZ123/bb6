import Raw11ExtraFamilySeed
namespace Raw11ExtraFamilyCoverage
open BB6Coverage BB6.Agent13BlankDelay
open Root56Coverage (center center_right center_left center_blank)
open Raw11ExtraFamily (move_a move_b move_c move_d move_e move_f)

def table (e : Bool) (f : Move) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨e,true,5⟩)
  | 5,false => some (some f)
  | _,_ => none

theorem step_center {e : Bool} {f : Move} {m : Machine} (hm : compatible (table e f) m) (c : Config) (r : Root56.Config)
    (h : Raw11ExtraFamily.step e f (center c) = some r) :
    ∃ s, rawStep m c = some s ∧ center s = r := by
  rcases f with ⟨w,d,q⟩
  have hq : c.state.val = 0 ∨ c.state.val = 1 ∨ c.state.val = 2 ∨ c.state.val = 3 ∨ c.state.val = 4 ∨ c.state.val = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> cases hb : c.tape c.head <;> cases d <;>
    simp [center,Root56.c,Raw11ExtraFamily.step,Raw11ExtraSweep.step,hq,hb] at h
  all_goals
    have ht := hm (readSlot c) _ (by simp only [table,hq,hb]; rfl)
    simp only [rawStep,ht,Bool.false_eq_true,ite_false,ite_true]
    exact ⟨_,rfl,by first | rw [center_right]; exact h | rw [center_left]; exact h⟩

theorem run_center {e : Bool} {f : Move} {m : Machine} (hm : compatible (table e f) m) (n : Nat) (c : Config) (r : Root56.Config)
    (h : Raw11ExtraFamily.run e f n (center c) = some r) :
    ∃ s, run m n c = some s ∧ center s = r := by
  induction n generalizing r with
  | zero => exact ⟨c,rfl,Option.some.inj h⟩
  | succ n ih =>
    rw [Raw11ExtraFamily.run_add] at h
    cases hr : Raw11ExtraFamily.run e f n (center c) with
    | none => simp [hr] at h
    | some r' =>
      obtain ⟨s,hs,hc⟩ := ih r' hr
      have hstep : Raw11ExtraFamily.step e f (center s) = some r := by
        rw [hc]
        simpa [hr,Raw11ExtraFamily.run] using h
      obtain ⟨s',hs',hc'⟩ := step_center hm s r hstep
      exact ⟨s',by rw [run.eq_2,hs]; exact hs',hc'⟩

theorem never_compatible {e : Bool} {f : Move} (hn : ∀ n, Raw11ExtraFamily.run e f n Root56.blank ≠ none)
    (m : Machine) (hm : compatible (table e f) m) : NeverHalts m := by
  intro n
  have hh := hn n
  rw [← center_blank] at hh
  cases h : Raw11ExtraFamily.run e f n (center blank) with
  | none => exact False.elim (hh h)
  | some r =>
    obtain ⟨s,hs,_⟩ := run_center hm n blank r h
    rw [hs]; rfl

theorem weighted (e : Bool) (f : Move) (B : Nat) (hn : ∀ n, Raw11ExtraFamily.run e f n Root56.blank ≠ none) : Cover (WeightedBound B) (table e f) :=
  .leaf _ fun m hm => weighted_never B m (never_compatible hn m hm)

def variant (v : Fin 6) : Bool × Move :=
  match v.val with
  | 0 => (false,move_a)
  | 1 => (false,move_b)
  | 2 => (true,move_c)
  | 3 => (true,move_d)
  | 4 => (true,move_e)
  | _ => (true,move_f)

def variantTable (v : Fin 6) : PartialMachine := table (variant v).1 (variant v).2

theorem variant_never (v : Fin 6) : ∀ n, Raw11ExtraFamily.run (variant v).1 (variant v).2 n Root56.blank ≠ none := by
  have h : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 ∨ v.val = 5 := by omega
  rcases h with h|h|h|h|h|h <;> simp only [variant,h]
  · exact Raw11ExtraFamily.never_a
  · exact Raw11ExtraFamily.never_b
  · exact Raw11ExtraFamily.never_c
  · exact Raw11ExtraFamily.never_d
  · exact Raw11ExtraFamily.never_e
  · exact Raw11ExtraFamily.never_f

theorem variantCover (v : Fin 6) (B : Nat) : Cover (WeightedBound B) (variantTable v) := weighted _ _ B (variant_never v)
#print axioms variantCover
end Raw11ExtraFamilyCoverage
