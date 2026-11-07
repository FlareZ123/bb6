import Std

namespace BB6.Agent49CanonicalRayRootDistanceArithmetic

def leftOddGap (d k t : Nat) : Int :=
  (t : Int) - (3 * (d : Int) - 5 - (k : Int))

def leftEvenGap (d k t : Nat) : Int :=
  (t : Int) - (3 * (d : Int) - 2 - (k : Int))

def rightOddGap (a k t : Nat) : Int :=
  2 * (t : Int) - (3 * (a : Int) - 1 - 2 * (k : Int))

def rightEvenGap (a k t : Nat) : Int :=
  2 * (t : Int) - (3 * (a : Int) - 2 - 2 * (k : Int))

/-- The canonical left-odd terminal gap differs from the old-ray distance
t_old - 2*d by exactly 9. -/
theorem leftOdd_gap_identity (a d k t s : Nat)
    (hCanonical : a = d + 5 + k + t)
    (hOldRay : a = 2 * d + 9 + s) :
    leftOddGap d k t = (s : Int) - 2 * (d : Int) + 9 := by
  unfold leftOddGap
  omega

/-- The canonical left-even terminal gap differs from the old-ray distance
t_old - 2*d by exactly 5. -/
theorem leftEven_gap_identity (a d k t s : Nat)
    (hCanonical : a = d + 2 + k + t)
    (hOldRay : a = 2 * d + 5 + s) :
    leftEvenGap d k t = (s : Int) - 2 * (d : Int) + 5 := by
  unfold leftEvenGap
  omega

/-- The canonical right-odd terminal gap is 2*(t_old-a)+1. -/
theorem rightOdd_gap_identity (a d k t s : Nat)
    (hCanonical : d = a + 1 + 2 * k + 2 * t)
    (hOldRay : d = 2 * a + 1 + 2 * s) :
    rightOddGap a k t = 2 * ((s : Int) - (a : Int)) + 1 := by
  unfold rightOddGap
  omega

/-- The canonical right-even terminal gap is 2*(t_old-a)+2. -/
theorem rightEven_gap_identity (a d k t s : Nat)
    (hCanonical : d = a + 2 + 2 * k + 2 * t)
    (hOldRay : d = 2 * a + 2 + 2 * s) :
    rightEvenGap a k t = 2 * ((s : Int) - (a : Int)) + 2 := by
  unfold rightEvenGap
  omega

/-- A left-odd root-ray separation bound excludes the canonical terminal
window once its width plus the fixed offset is smaller than the distance bound. -/
theorem leftOdd_window_excluded (a d k t s W R : Nat)
    (hCanonical : a = d + 5 + k + t)
    (hOldRay : a = 2 * d + 9 + s)
    (hRootDistance : (R : Int) ≤ (s : Int) - 2 * (d : Int) ∨
      (s : Int) - 2 * (d : Int) ≤ -(R : Int))
    (hWindowLo : -(W : Int) ≤ leftOddGap d k t)
    (hWindowHi : leftOddGap d k t ≤ (W : Int))
    (hLarge : W + 9 < R) : False := by
  have hGap := leftOdd_gap_identity a d k t s hCanonical hOldRay
  have hLo : -((W + 9 : Nat) : Int) ≤ leftOddGap d k t - 9 := by omega
  have hHi : leftOddGap d k t - 9 ≤ ((W + 9 : Nat) : Int) := by omega
  rcases hRootDistance with hRoot | hRoot <;> omega

/-- A left-even root-ray separation bound excludes the canonical terminal
window once its width plus the fixed offset is smaller than the distance bound. -/
theorem leftEven_window_excluded (a d k t s W R : Nat)
    (hCanonical : a = d + 2 + k + t)
    (hOldRay : a = 2 * d + 5 + s)
    (hRootDistance : (R : Int) ≤ (s : Int) - 2 * (d : Int) ∨
      (s : Int) - 2 * (d : Int) ≤ -(R : Int))
    (hWindowLo : -(W : Int) ≤ leftEvenGap d k t)
    (hWindowHi : leftEvenGap d k t ≤ (W : Int))
    (hLarge : W + 5 < R) : False := by
  have hGap := leftEven_gap_identity a d k t s hCanonical hOldRay
  have hLo : -((W + 5 : Nat) : Int) ≤ leftEvenGap d k t - 5 := by omega
  have hHi : leftEvenGap d k t - 5 ≤ ((W + 5 : Nat) : Int) := by omega
  rcases hRootDistance with hRoot | hRoot <;> omega

/-- A right-odd root-ray separation bound excludes the canonical terminal
window once its width plus one is smaller than twice the distance bound. -/
theorem rightOdd_window_excluded (a d k t s W R : Nat)
    (hCanonical : d = a + 1 + 2 * k + 2 * t)
    (hOldRay : d = 2 * a + 1 + 2 * s)
    (hRootDistance : (R : Int) ≤ (s : Int) - (a : Int) ∨
      (s : Int) - (a : Int) ≤ -(R : Int))
    (hWindowLo : -(W : Int) ≤ rightOddGap a k t)
    (hWindowHi : rightOddGap a k t ≤ (W : Int))
    (hLarge : W + 1 < 2 * R) : False := by
  have hGap := rightOdd_gap_identity a d k t s hCanonical hOldRay
  rcases hRootDistance with hRoot | hRoot <;> omega

/-- A right-even root-ray separation bound excludes the canonical terminal
window once its width plus two is smaller than twice the distance bound. -/
theorem rightEven_window_excluded (a d k t s W R : Nat)
    (hCanonical : d = a + 2 + 2 * k + 2 * t)
    (hOldRay : d = 2 * a + 2 + 2 * s)
    (hRootDistance : (R : Int) ≤ (s : Int) - (a : Int) ∨
      (s : Int) - (a : Int) ≤ -(R : Int))
    (hWindowLo : -(W : Int) ≤ rightEvenGap a k t)
    (hWindowHi : rightEvenGap a k t ≤ (W : Int))
    (hLarge : W + 2 < 2 * R) : False := by
  have hGap := rightEven_gap_identity a d k t s hCanonical hOldRay
  rcases hRootDistance with hRoot | hRoot <;> omega

#print axioms leftOdd_gap_identity
#print axioms leftEven_gap_identity
#print axioms rightOdd_gap_identity
#print axioms rightEven_gap_identity
#print axioms leftOdd_window_excluded
#print axioms leftEven_window_excluded
#print axioms rightOdd_window_excluded
#print axioms rightEven_window_excluded

end BB6.Agent49CanonicalRayRootDistanceArithmetic
