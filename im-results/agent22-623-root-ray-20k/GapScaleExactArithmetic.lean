import Std

namespace BB6.Agent22GapScaleExactArithmetic

def gap (a d : Nat) : Int :=
  if d ≤ a then (a : Int) - 4 * (d : Int)
  else (d : Int) - 4 * (a : Int)

def scale (a d : Nat) : Nat := min a d

def beta (B c v : Nat) : Int := (B : Int) - (c : Int) - (v : Int)

def delta (E m : Nat) : Int := (E : Int) - 3 * (m : Int)

/-- Exact left-output update. `u` is the actual ray shift and `v` is the
scaled canonical exponent; no approximation or error term is hidden. -/
theorem left_update (m c v u B E : Nat) (g : Int)
    (hgap : g = (u : Int) + (c : Int) + (v : Int) - 3 * (m : Int))
    (hleft : E ≤ B + u) :
    gap (B + u) E = g - 9 * (m : Int) + beta B c v - 4 * delta E m ∧
    (scale (B + u) E : Int) = 3 * (m : Int) + delta E m := by
  constructor
  · simp [gap, hleft, beta, delta]
    omega
  · simp [scale, Nat.min_eq_right hleft, delta]
    omega

/-- Exact right-output update. `u` is the actual ray shift and `v` is the
scaled canonical exponent; no approximation or error term is hidden. -/
theorem right_update (m c v u B E : Nat) (g : Int)
    (hgap : g = (u : Int) + (c : Int) + (v : Int) - 3 * (m : Int))
    (hright : B + u < E) :
    gap (B + u) E = -4 * g - 9 * (m : Int) + delta E m - 4 * beta B c v ∧
    (scale (B + u) E : Int) = 3 * (m : Int) + g + beta B c v := by
  constructor
  · simp [gap, Nat.not_le_of_gt hright, beta, delta]
    omega
  · simp [scale, Nat.min_eq_left (Nat.le_of_lt hright), beta]
    omega

#print axioms left_update
#print axioms right_update

end BB6.Agent22GapScaleExactArithmetic
