import Std

namespace BB6.Agent49CanonicalRayArithmetic

/-- On a minimal far-left odd ray, the ratio-four predecessor window is exactly a window for the shift near 3*d-5-k. -/
theorem farLeftOddShiftWindow (d k t W : Nat) :
    (-(W : Int) ≤ 4*(d : Int) - ((d : Int) + 5 + (k : Int) + (t : Int)) ∧
      4*(d : Int) - ((d : Int) + 5 + (k : Int) + (t : Int)) ≤ (W : Int)) ↔
    (-(W : Int) ≤ (t : Int) - (3*(d : Int) - 5 - (k : Int)) ∧
      (t : Int) - (3*(d : Int) - 5 - (k : Int)) ≤ (W : Int)) := by
  omega

/-- On a minimal far-left even ray, the ratio-four predecessor window is exactly a window for the shift near 3*d-2-k. -/
theorem farLeftEvenShiftWindow (d k t W : Nat) :
    (-(W : Int) ≤ 4*(d : Int) - ((d : Int) + 2 + (k : Int) + (t : Int)) ∧
      4*(d : Int) - ((d : Int) + 2 + (k : Int) + (t : Int)) ≤ (W : Int)) ↔
    (-(W : Int) ≤ (t : Int) - (3*(d : Int) - 2 - (k : Int)) ∧
      (t : Int) - (3*(d : Int) - 2 - (k : Int)) ≤ (W : Int)) := by
  omega

/-- On a minimal far-right odd ray, twice the shift is close to 3*a-1-2*k exactly when the ratio-four predecessor window holds. -/
theorem farRightOddShiftWindow (a k t W : Nat) :
    (-(W : Int) ≤ 4*(a : Int) - ((a : Int) + 1 + 2*(k : Int) + 2*(t : Int)) ∧
      4*(a : Int) - ((a : Int) + 1 + 2*(k : Int) + 2*(t : Int)) ≤ (W : Int)) ↔
    (-(W : Int) ≤ 2*(t : Int) - (3*(a : Int) - 1 - 2*(k : Int)) ∧
      2*(t : Int) - (3*(a : Int) - 1 - 2*(k : Int)) ≤ (W : Int)) := by
  omega

/-- On a minimal far-right even ray, twice the shift is close to 3*a-2-2*k exactly when the ratio-four predecessor window holds. -/
theorem farRightEvenShiftWindow (a k t W : Nat) :
    (-(W : Int) ≤ 4*(a : Int) - ((a : Int) + 2 + 2*(k : Int) + 2*(t : Int)) ∧
      4*(a : Int) - ((a : Int) + 2 + 2*(k : Int) + 2*(t : Int)) ≤ (W : Int)) ↔
    (-(W : Int) ≤ 2*(t : Int) - (3*(a : Int) - 2 - 2*(k : Int)) ∧
      2*(t : Int) - (3*(a : Int) - 2 - 2*(k : Int)) ≤ (W : Int)) := by
  omega

#print axioms farLeftOddShiftWindow
#print axioms farLeftEvenShiftWindow
#print axioms farRightOddShiftWindow
#print axioms farRightEvenShiftWindow

end BB6.Agent49CanonicalRayArithmetic
