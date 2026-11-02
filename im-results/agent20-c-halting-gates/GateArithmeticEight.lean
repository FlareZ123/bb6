import GateArithmetic

namespace Agent20Gate

private theorem pow_two_mod_eight (n : Nat) : 2^(n+3)%8=0 := by
  have h : 2^(n+3)=2^n*8 := by rw [Nat.pow_add]
  rw [h]
  simp

/-- The low exponent class 4 mod 8 forces a multiple-of-eight right counter. -/
theorem low_m_four_mod_eight (m k : Nat)
    (he : k+3*m+4=2^(2*m+3)) (hm : m%8=4) : k%8=0 := by
  have hp : 2^(2*m+3)%8=0 := by
    exact pow_two_mod_eight (2*m)
  omega

/-- The high parameter class m even, j+3m=3 mod 8 forces a
    left counter 1 mod 4 and right counter 0 mod 8. -/
theorem high_m_even_mod_eight (j m k : Nat)
    (he : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hm : m%2=0) (hj : (j+3*m)%8=3) :
    j%2=1 ∧ k%8=0 := by
  have hodd : j%2=1 := by omega
  constructor
  · exact hodd
  · cases m with
    | zero =>
        simp at he
        omega
    | succ n =>
        have hp : (2^(2*(n+1)+2)*(j+3))%8=0 := by
          have hpow : 2*(n+1)+2=(2*n+1)+3 := by omega
          rw [hpow, Nat.mul_mod, pow_two_mod_eight]
          simp
        omega

end Agent20Gate
#print axioms Agent20Gate.low_m_four_mod_eight
#print axioms Agent20Gate.high_m_even_mod_eight
