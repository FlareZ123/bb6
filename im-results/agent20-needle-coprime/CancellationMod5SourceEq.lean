import CancellationMod5
import Lean.Elab.Tactic.Omega

namespace CancellationModFive
open CancellationNat CancellationGap CancellationStrip CancellationConstructive

/-- An exact cancellation source odd part, including an original-source
high-level terminal feeder, has no parent at the four mod20 cylinders. -/
theorem source_equation_inverse_mod5
    (r u q : Nat) (hr : 1≤r)
    (hupper : u+1≤2*r*valuationA r)
    (hfour : u%4=0) (hfive : u%5≠4)
    (heq : (2^(valuationA r)+3)*(2*q+3)+9^r =
       (2^(valuationA r))^(2*r)) :
    ¬ (2^(u+1)+3) ∣
       (2^(valuationA r)*(2*q+3)+3-2*u) := by
  let A:=2^(valuationA r)
  have hA : 3≤A := by
    have hp := exp_mono 3 (valuationA r) (by
      have hv:=valuationA_linear r
      omega)
    dsimp [A]
    omega
  have he : (A+3)*P A r+9^r=A^(2*r) :=
    CancellationNat.exact A r hA
  change (A+3)*(2*q+3)+9^r=A^(2*r) at heq
  have hm : (A+3)*(2*q+3)=(A+3)*P A r := by omega
  have hq : 2*q+3=P A r :=
    Nat.mul_left_cancel (by omega : 0<A+3) hm
  rw [hq]
  exact uniform_inverse_mod5 r u hr hupper hfour hfive

#print axioms source_equation_inverse_mod5
end CancellationModFive
