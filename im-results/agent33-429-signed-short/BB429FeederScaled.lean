import BB429UnboundedFeeder

namespace BB429FeederScaled
open BB429UnboundedFeeder

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-!
# Full-parameter, true-source inverse depth under a 16-adic congruence.

The source-correct four-transition S-F-E-F block yields nonblank
ancestry of *arbitrary* depth for all 15-line parameters divisible
by 48*16^n, not just the single sequence q=3*16^(n+1).
This is an existence theorem for authentic accelerator paths with
an arbitrary starting state; the start is not proved reachable from blank.
-/

/-- A uniform construction for all positive multipliers of the 16-adic
    offset, not just the t=1 seed of the first FEFS certificate. -/
theorem arbitrary_inverse_depth_scaled (n : Nat) :
    ∀ (z t : Nat), 1 ≤ t →
      ∃ s : BB429.State,
        BB429.run (4*n) s = some (anchor z (16^n*t)) := by
  induction n with
  | zero =>
    intro z t ht
    refine ⟨anchor z t, ?_⟩
    simp [BB429.run]
  | succ n ih =>
    intro z t ht
    let v := 16^n*t
    have hv : 1 ≤ v := by
      dsimp [v]
      have hp : 0 < 16^n := Nat.pow_pos (by omega)
      have hmul : 0 < 16^n*t := Nat.mul_pos hp (by omega)
      omega
    obtain ⟨s,hs⟩ := ih (z+960*v-1) t ht
    refine ⟨s, ?_⟩
    have hp : 16^(n+1)*t = 16*v := by
      dsimp [v]
      rw [Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hstep := source_four_step z v hv
    rw [show 4*(n+1)=4*n+4 by omega, BB429.run_add, hs]
    simp only [Option.bind_some]
    rw [hp]
    exact hstep

/-- Every q divisible by 48*16^n has at least 4n source-correct
    predecessor steps on the *actual 15 odd-reset line*. No black-box
    symbolic signed approximation or finite-state simulation. -/
theorem branch15_all_multiples_have_deep_predecessors (n t : Nat)
    (ht : 1 ≤ t) :
    ∃ s : BB429.State,
      BB429.run (4*n) s =
        some (32*(48*(16^n*t))+15,64*(48*(16^n*t))+27) := by
  let v := 16^n*t
  let q := 48*v
  obtain ⟨s,hs⟩ := arbitrary_inverse_depth_scaled n (4*q) t ht
  have heq : anchor (4*q) v = (32*q+15,64*q+27) := by
    dsimp [anchor,q]
    apply Prod.ext <;> omega
  refine ⟨s, ?_⟩
  rw [show 16^n*t=v by rfl] at hs
  rw [heq] at hs
  exact hs

#print axioms arbitrary_inverse_depth_scaled
#print axioms branch15_all_multiples_have_deep_predecessors
end BB429FeederScaled
