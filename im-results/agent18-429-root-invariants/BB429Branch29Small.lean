import BB429FiniteAvoidance
import BB429Reset31
import Lean.Elab.Tactic.Omega

/-!
# A certified global exclusion for all 21 previously unclassified
small parameters of the #429 29(mod32) odd reset family.

A 553-step exact blank-root accelerator prefix ends at rank 2676,
strictly above the greatest small target's rank 2673. The whole prefix
avoids each of the 21 target states (32q+29,64q+55), q<21. The
rank-cutoff theorem makes all these exclusions *global*, not finite.
-/
namespace BB429Branch29Small
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
open BB429Reset31

theorem small_avoidance_certificate :
    (List.range 21).all (fun q =>
      BB429FiniteAvoidance.avoid (32*q+29,64*q+55) 553 (0,0)) = true := by
  decide

theorem no_small_q (q : Nat) (hq : q<21) :
    ¬Reach (32*q+29) (64*q+55) := by
  have htrace : BB429.run 553 (0,0) = some (221,2234) := by
    decide
  have hav : BB429FiniteAvoidance.avoid
      (32*q+29,64*q+55) 553 (0,0) = true :=
    (List.all_eq_true.mp small_avoidance_certificate)
      q (List.mem_range.mpr hq)
  have hfar : BB429.rank (32*q+29,64*q+55) <
      BB429.rank (221,2234) := by
    simp only [BB429.rank]
    omega
  exact BB429FiniteAvoidance.no_reach_of_avoid
    (32*q+29,64*q+55) 553 (0,0) (221,2234)
    htrace hav hfar

#print axioms small_avoidance_certificate
#print axioms no_small_q
end BB429Branch29Small
