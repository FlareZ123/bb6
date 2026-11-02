import P1R54Gap
import P1R54Generated

namespace BB6.Agent47P1

/-- Exact source hub identity for all q, including q=0. -/
theorem r54_root_identity (q:Nat) :
    r54b0 (r54S q) = 14*2^(65536*q+54)-2*(65536*q+54)-16 := by
  have hs := r54S_shift q
  have hx := r54X_growth q
  have hpow : (2:Nat)^(65536*q+54)=65536*r54X q := by
    unfold r54X
    rw [show 65536*q+54=(65536*q+38)+16 by omega,Nat.pow_add]
    simp only [show (2:Nat)^16=65536 by decide]
    omega
  unfold r54b0
  rw [hpow]
  omega

#print axioms r54_root_identity
end BB6.Agent47P1
