import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
A constant-size all-depth invariant of the exact F321 source-counter map:
the second counter is never 0 mod 3 from authentic seed (1,1).
This gives a new gate exclusion class independent of dyadic inverse rays.
-/

namespace BB6.Agent2F321Mod3
open BB6.Agent31F321Density

theorem counter_nonzero_mod3_preserved
    {a d A D:Nat} (h:CounterMove a d A D)
    (hd:d%3≠0) : D%3≠0 := by
  cases h with
  | high hg => omega
  | equal => omega
  | far h1 h2 => omega
  | middleEven h1 h2 hp => omega
  | middleOdd h1 h2 hp => omega

theorem source_orbit_nonzero_mod3
    {n a d:Nat} (h:CounterReach 1 1 n a d) : d%3≠0 := by
  induction h with
  | nil => decide
  | step hr hm ih =>
    exact counter_nonzero_mod3_preserved hm ih

/-- Every source-map halt gate with d divisible by three is excluded
at all finite times, without any lower cutoff. -/
theorem multiple_three_gate_never (k:Nat) :
    ∀ n, ¬CounterReach 1 1 n (3*k+1) (3*k) := by
  intro n hr
  have hd := source_orbit_nonzero_mod3 hr
  omega

/-- In particular, the simple two-step H/F live ray is NOT reachable
from the authentic F321 source-counter seed. -/
theorem high_far_ray_unreachable (k:Nat) :
    ∀ n, ¬CounterReach 1 1 n (4*k+2) (3*k) := by
  intro n hr
  exact multiple_three_gate_never k n (by simpa using hr)

#print axioms counter_nonzero_mod3_preserved
#print axioms source_orbit_nonzero_mod3
#print axioms multiple_three_gate_never
#print axioms high_far_ray_unreachable

end BB6.Agent2F321Mod3
