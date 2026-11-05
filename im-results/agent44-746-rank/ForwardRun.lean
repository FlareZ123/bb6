import RootDepth
set_option maxHeartbeats 0
namespace CascadeRank
open CascadeResetInverse CascadeSweep CascadeManyShield

/-- Unique total first-outcome choice, halting represented as `none`.
    Its source equivalence is proved below without executable search. -/
noncomputable def nextReset (h : Nat) : Option Nat :=
  Classical.choose (first_outcome_exists h)

private theorem nextReset_sound (h : Nat) : Outcome (h,0) (nextReset h) :=
  Classical.choose_spec (first_outcome_exists h)

/-- A non-halting first-reset successor is exactly the source-certified
    genuine first-return grammar; choice cannot change deterministic behavior. -/
theorem nextReset_iff_parent (h u : Nat) :
    nextReset h = some u ↔ ResetParent h u := by
  constructor
  · intro he
    have hs : Outcome (h,0) (some u) := he ▸ (nextReset_sound h)
    exact (reset_parent_iff h u).mp hs
  · intro hp
    exact outcome_unique (nextReset_sound h) ((reset_parent_iff h u).mpr hp)

/-- A single deterministic forward reset trajectory, with `none` after halt. -/
noncomputable def runResets (start : Nat) : Nat → Option Nat
  | 0 => some start
  | n+1 => (runResets start n).bind nextReset

/-- Backward witness paths are equivalent, length for length, to the unique
    forward reset trajectory, without searching over inverse branches. -/
theorem reverse_path_iff_forward_run (u start n : Nat) :
    ReversePath u start n ↔ runResets start n = some u := by
  induction n generalizing u with
  | zero =>
    constructor
    · intro hp
      cases hp with
      | stop _ => rfl
    · intro hh
      have h : start=u := by simpa [runResets] using hh
      subst u
      exact ReversePath.stop _
  | succ n ih =>
    constructor
    · intro hp
      cases hp with
      | @extend u h v steps hr ht =>
        have hh : runResets start n = some h := (ih h).mp ht
        simp [runResets, hh, (nextReset_iff_parent h u).mpr hr]
    · intro hh
      change (runResets start n).bind nextReset = some u at hh
      cases heq : runResets start n with
      | none => simp [heq] at hh
      | some h =>
        have hs : nextReset h = some u := by simpa [heq] using hh
        exact ReversePath.extend ((nextReset_iff_parent h u).mp hs)
          ((ih h).mpr heq)

/-- An exact blank-origin fatal state is visited within a polynomially
    bounded number of deterministic source first-reset episodes. -/
theorem root_fatal_iff_bounded_forward_run (n : Nat) (hn : 2≤n) :
    ReachC (2,0) (fatal n,0) ↔
      ∃ steps, steps≤(n+2)^2 ∧ runResets 2 steps = some (fatal n) := by
  rw [root_fatal_iff_bounded_reverse_path n hn]
  simp only [reverse_path_iff_forward_run]

#print axioms nextReset_iff_parent
#print axioms reverse_path_iff_forward_run
#print axioms root_fatal_iff_bounded_forward_run
end CascadeRank
