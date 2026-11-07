import Std

/-!
Standalone Lean 4.36.0-rc2 arithmetic certificate for the exact affine
identity of a generic Sheep first-even section branch. Given x=2^a*u
and the exact cofactor equation for a branch with odd-block length h,
it verifies

  2^(a+h+1) * (1+3^h*v)
    = 3^h*(1+2^(a+1))*x +
      2^a*(2^(h+1)+3^h*(2*a-3)).

This is the identity used to transport odd-q residues in the all-even-
modulus finite-path lifting proof. It is not an original-machine source
import, a proof of branch existence, or a BB(6) decision.
-/

namespace SheepAffineBranch

theorem generic_even_affine
    (a h : Nat) (x u v : Int)
    (hx : x = (2:Int)^a * u)
    (hv : (2:Int)^(h+1)*v = ((2:Int)^(a+1)+1)*u + 2*(a:Int)-3) :
    (2:Int)^(a+h+1)*(1+(3:Int)^h*v) =
      (3:Int)^h*(1+(2:Int)^(a+1))*x +
      (2:Int)^a*((2:Int)^(h+1)+(3:Int)^h*(2*(a:Int)-3)) := by
  have ha : (2:Int)^(a+h+1) = (2:Int)^a*(2:Int)^(h+1) := by
    have hh : a+h+1=a+(h+1) := by omega
    rw [hh,Int.pow_add]
  rw [ha, hx]
  grind

#print axioms generic_even_affine

end SheepAffineBranch
