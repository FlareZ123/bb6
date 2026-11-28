import Lean

namespace BB429SignedFinite

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

/-- Overapproximation of the source's signed inverse blocks: F, EF, SF.
    All guards and state equations are linear over natural numbers.
    We intentionally do NOT assume Bad predicates; an excluded path here
    is excluded in every soundly pruned source inverse graph. -/
def Step (u d v e : Nat) : Prop :=
  (u % 2 = 0 ∧ 2*v = u ∧ e = d+3*u+3) ∨
  (u % 2 = 1 ∧ d % 8 = 0 ∧ 8*v = 8*u+d+8 ∧ 4*e = d+16) ∨
  (u % 2 = 0 ∧ d % 8 = 4 ∧ 8*v = 8*u+d+20 ∧ 4*e+4 = d)

/-- Entire affine family has no length-4 path in the full
    algebraically possible F/EF/SF system, even BEFORE Bad pruning. -/
theorem branch13_mod4_zero_no_four
    (k u1 d1 u2 d2 u3 d3 u4 d4 : Nat)
    (hk : k % 4 = 0)
    (h1 : Step (48*k+24) (96*k+66) u1 d1)
    (h2 : Step u1 d1 u2 d2)
    (h3 : Step u2 d2 u3 d3)
    (h4 : Step u3 d3 u4 d4) : False := by
  unfold Step at *
  omega

/-- Entire affine family has no length-5 path in the full
    algebraically possible F/EF/SF system, even BEFORE Bad pruning. -/
theorem branch13_mod4_one_no_five
    (k u1 d1 u2 d2 u3 d3 u4 d4 u5 d5 : Nat)
    (hk : k % 4 = 1)
    (h1 : Step (48*k+24) (96*k+66) u1 d1)
    (h2 : Step u1 d1 u2 d2)
    (h3 : Step u2 d2 u3 d3)
    (h4 : Step u3 d3 u4 d4)
    (h5 : Step u4 d4 u5 d5) : False := by
  unfold Step at *
  omega

/-- Entire affine family has no length-4 path in the full
    algebraically possible F/EF/SF system, even BEFORE Bad pruning. -/
theorem branch15_mod4_zero_no_four
    (k u1 d1 u2 d2 u3 d3 u4 d4 : Nat)
    (hk : k % 4 = 0)
    (h1 : Step (48*k+39) (96*k+96) u1 d1)
    (h2 : Step u1 d1 u2 d2)
    (h3 : Step u2 d2 u3 d3)
    (h4 : Step u3 d3 u4 d4) : False := by
  unfold Step at *
  omega

/-- Entire affine family has no length-6 path in the full
    algebraically possible F/EF/SF system, even BEFORE Bad pruning. -/
theorem branch15_mod8_one_no_six
    (k u1 d1 u2 d2 u3 d3 u4 d4 u5 d5 u6 d6 : Nat)
    (hk : k % 8 = 1)
    (h1 : Step (48*k+39) (96*k+96) u1 d1)
    (h2 : Step u1 d1 u2 d2)
    (h3 : Step u2 d2 u3 d3)
    (h4 : Step u3 d3 u4 d4)
    (h5 : Step u4 d4 u5 d5)
    (h6 : Step u5 d5 u6 d6) : False := by
  unfold Step at *
  omega

#print axioms branch13_mod4_zero_no_four
#print axioms branch13_mod4_one_no_five
#print axioms branch15_mod4_zero_no_four
#print axioms branch15_mod8_one_no_six
end BB429SignedFinite
