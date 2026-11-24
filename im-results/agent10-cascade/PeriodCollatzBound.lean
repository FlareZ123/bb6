import Std

namespace CascadeCollatzBound

/-- Lower rational bound for ln(t), t>1, from 64 terms of the
    atanh series with x=(t-1)/(t+1). -/
def logLower (t : Rat) : Rat :=
  let x := (t-1)/(t+1)
  (List.range 64).foldl (fun s j => s + 2*x^(2*j+1)/(2*j+1 : Nat)) 0

/-- Upper bound adds a geometric tail estimate; the analytic inequality
    is supplied in the paper, while the following numeric checks are kernel verified. -/
def logUpper (t : Rat) : Rat :=
  let x := (t-1)/(t+1)
  logLower t + 2*x^129/(129*(1-x*x))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem lower_rational_check :
    (103768467013 : Rat)/65470613321 < logLower 3 / logUpper 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem upper_rational_check :
    logUpper 3 / logLower 2 + 1/(2:Rat)^72 < (10439860591:Rat)/6586818670 := by
  decide +kernel

/-- The bounding fractions are Farey neighbors. Any fraction strictly
    between them has denominator at least the sum of their denominators. -/
theorem farey_den_bound (N A : Nat)
    (lo : 103768467013*A < 65470613321*N)
    (hi : 6586818670*N < 10439860591*A) : 72057431991 ≤ A := by
  omega

/-- The strict lower slope-product bound D/A > log2(3)-1 transfers
    the odd-step bound into a lower bound on the sweep increment. -/
theorem sweep_lower_bound (A D : Nat)
    (hA : 72057431991 ≤ A)
    (hD : (103768467013-65470613321)*A < 65470613321*D) :
    42150895613 ≤ D := by omega

end CascadeCollatzBound

#print axioms CascadeCollatzBound.lower_rational_check
#print axioms CascadeCollatzBound.upper_rational_check
#print axioms CascadeCollatzBound.farey_den_bound
#print axioms CascadeCollatzBound.sweep_lower_bound
