import Lean
import Lean.Elab.Tactic.Omega

/-!
An exact integer polynomial for the Space Needle cancellation feeder.
For B = 2^(v+1), v = (9^r+3)/2, the odd value
  polynomial B r = 2*q+3
encodes the cancellation feeder without dividing two giant integers.

The identity is valid for all integer B, not merely powers of two.
The terminal-feeder/source bridge is proved separately by the existing
NeedleVariableValuation source chain; this file is pure arithmetic.
-/

namespace CancellationSparse

def polynomial (B : Int) : Nat → Int
  | 0 => 0
  | r+1 => B^2 * polynomial B r + (9:Int)^r * (B-3)

theorem exact (B : Int) (r : Nat) :
    (B+3)*polynomial B r + (9:Int)^r = B^(2*r) := by
  induction r with
  | zero => simp [polynomial]
  | succ r ih =>
    calc
      (B+3)*polynomial B (r+1) + (9:Int)^(r+1)
          = B^2 * ((B+3)*polynomial B r + (9:Int)^r) := by
              simp only [polynomial, Int.pow_succ]
              grind
      _ = B^2 * B^(2*r) := by rw [ih]
      _ = B^(2*(r+1)) := by
        rw [show 2*(r+1)=2*r+2 by omega, Int.pow_add]
        exact Int.mul_comm _ _

#print axioms exact
end CancellationSparse
