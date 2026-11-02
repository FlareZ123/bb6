import Std

namespace Agent20Gate

private theorem pow_two_mod_four (n : Nat) : 2^(n+2) % 4 = 0 := by
  have h : 2^(n+2) = 2^n * 4 := by
    rw [Nat.pow_add]
  rw [h]
  simp

/-- Low-branch exponent 1 mod 4 yields an odd right counter and a forbidden sum. -/
theorem low_mod_one (m k : Nat)
    (he : k + 3*m + 4 = 2^(2*m+3)) (hm : m%4=1) :
    k%2=1 ∧ (1+k)%4=2 := by
  have hp : 2^(2*m+3)%4=0 := by
    have heq : 2*m+3=(2*m+1)+2 := by omega
    rw [heq]
    exact pow_two_mod_four _
  omega

/-- High-branch parameter sum 0 mod 4 forces the same forbidden configuration. -/
theorem high_mod_zero (j m k : Nat)
    (he : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hm : (j+m)%4=0) :
    k%2=1 ∧ (2*j+3+k)%4=2 := by
  have hp : (2^(2*m+2)*(j+3))%4=0 := by
    rw [Nat.mul_mod, pow_two_mod_four]
    simp
  omega

end Agent20Gate
#print axioms Agent20Gate.low_mod_one
#print axioms Agent20Gate.high_mod_zero
