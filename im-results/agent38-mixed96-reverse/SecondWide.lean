import SecondMod96
namespace A38Mixed96

theorem second_wide_parameter_residues (j m k : Nat)
    (hj : j % 12 = 0) (hm : m % 8 = 4)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ((2*j+3)%48=3 ∧ k%24=7) ∨
    ((2*j+3)%48=27 ∧ k%24=19) := by
  have hm2 : 2 ≤ m := by omega
  have hp := A41.pow_even_ge6_mod96 m hm2
  have hr : (k+j+3*m+5)%96=(64*(j+3))%96 := by
    rw [heq, Nat.mul_mod, hp]
    omega
  omega

#print axioms second_wide_parameter_residues
end A38Mixed96
