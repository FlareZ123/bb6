import Agent8RootCancellationBudgetBridge
import Lean.Elab.Tactic.Omega

/-!
# Near-q scale orientation transfer at n=10

The terminal-window/bridge composition produces one of two ratio-four
strips. Either strip forces the first coordinate of a near q state to be
the smaller coordinate, so the n=10 scale band transfers from min(q₁,q₂)
to q₁ as required by the near root-mass wrappers.
-/

namespace BB6.Agent48NearScaleTransferN10

open BB6.Agent8RootCancellationBudgetBridge

/-- A far terminal parent combined with a near q bridge cannot have q₁>q₂. -/
theorem near_far_orientation (u v : Nat)
    (hmLo : 19680 <= min u v)
    (hgap : absDiff v (13*u) <= 470) :
    u <= v := by
  by_contra h
  have hvu : v < u := by omega
  have hmin : min u v = v := by simp [min_eq_right (by omega : v <= u)]
  have hvLo : 19680 <= v := by simpa [hmin] using hmLo
  have hg := absDiff_le_both v (13*u) 470 hgap
  omega

/-- A near terminal parent combined with a near q bridge cannot have q₁>q₂. -/
theorem near_near_orientation (u v : Nat)
    (hmLo : 19680 <= min u v)
    (hgap : absDiff (7*u) (4*v) <= 470) :
    u <= v := by
  by_contra h
  have hvu : v < u := by omega
  have hmin : min u v = v := by simp [min_eq_right (by omega : v <= u)]
  have hvLo : 19680 <= v := by simpa [hmin] using hmLo
  have hg := absDiff_le_both (7*u) (4*v) 470 hgap
  omega

#print axioms near_far_orientation
#print axioms near_near_orientation

end BB6.Agent48NearScaleTransferN10
