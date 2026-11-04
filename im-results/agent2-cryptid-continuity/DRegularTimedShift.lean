import Lean.Elab.Tactic.Omega
import DRegularDurationShift

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.DRegularTimedShift
open DRegular BB6.DRegularShift BB6.DRegularDurationShift

def quadCoeff : Nat → Nat
 | 0 => 0
 | n+1 => 12*(3^n)*(3^n) + 64*quadCoeff n

def linearCoeff : Nat → L → Nat
 | 0, _ => 0
 | n+1, s => (3^n)*slope s + 8*linearCoeff n ((next s).getD s)

private theorem combine (D E L U M Q p : Nat) :
    (D + (E*L)*p + 12*(E*p)*(E*p)) +
    (U + M*(8*p) + Q*(8*p)*(8*p)) =
    (D+U) + (E*L+8*M)*p + (12*E*E+64*Q)*p*p := by
  have h1 : 12*(E*p)*(E*p) = (12*E*E)*p*p := by ac_rfl
  have h2 : Q*(8*p)*(8*p) = (64*Q)*p*p := by
    calc
      Q*(8*p)*(8*p) = (8*8*Q)*p*p := by ac_rfl
      _ = (64*Q)*p*p := by rfl
  have h3 : M*(8*p)=(8*M)*p := by ac_rfl
  rw [h1,h2,h3]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega
