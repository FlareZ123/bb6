import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth

/-- Every even exponent 2m+2 makes the corresponding power of two
    congruent to one modulo three. -/
private theorem pow_even_mod_three (m : Nat) :
    (2^(2*m+2))%3=1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2*(m+1)+2=(2*m+2)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega

/-- Every natural power of two is a nonzero residue modulo three. -/
private theorem pow_two_mod_three (n : Nat) :
    2^n%3=1 ∨ 2^n%3=2 := by
  induction n with
  | zero => exact Or.inl (by decide)
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_mod]
    rcases ih with h | h
    · right
      omega
    · left
      omega

/-- Both of the two complete Machine C stopping-input equations
    force the second coordinate to be one modulo three. -/
theorem first_stopping_k_mod_three (m k : Nat)
    (hgate : k+3*m+4=2^(2*m+3)) : k%3=1 := by
  have hpower : (2^(2*m+3))%3=2 := by
    have he : 2*m+3=(2*m+2)+1 := by omega
    rw [he,Nat.pow_succ,Nat.mul_mod,pow_even_mod_three m]
    omega
  have hrest : (k+3*m+4)%3=2 := by
    rw [hgate]
    exact hpower
  omega

theorem second_stopping_k_plus_two_mod_three (j m k : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (k+2)%3=0 := by
  have hpower := pow_even_mod_three m
  have hmod : (k+j+3*m+5)%3=(j+3)%3 := by
    rw [hgate,Nat.mul_mod,hpower]
    omega
  omega

/-- The right counter of a legitimate second stopping input plus two
    can never itself be a power of two. -/
theorem second_stopping_not_power_of_two (j m k d : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    k+2 ≠ 2^d := by
  intro hpow
  have hdiv := second_stopping_k_plus_two_mod_three j m k hgate
  rw [hpow] at hdiv
  rcases pow_two_mod_three d with h | h
  · omega
  · omega

/-- Algebraically, any exact affine chain in a second stopping input
    retains the factor of three in its residual right counter plus two. -/
theorem second_stopping_affine_residual_mod_three
    (j m k d y : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hscale : 2^d*(y+2)=k+2) :
    (y+2)%3=0 := by
  have hdiv : (2^d*(y+2))%3=0 := by
    rw [hscale]
    exact second_stopping_k_plus_two_mod_three j m k hgate
  rcases pow_two_mod_three d with h | h
  · rw [Nat.mul_mod,h] at hdiv
    omega
  · rw [Nat.mul_mod,h] at hdiv
    omega

/-- If the terminal affine right counter has the source-certified
    0-mod-4 or exactly-two shape, the stopping equation rules out
    the exactly-two case and rules out zero as well. -/
theorem second_stopping_affine_residual_ge_four
    (j m k d y : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hscale : 2^d*(y+2)=k+2)
    (hshape : y=2 ∨ y%4=0) :
    4≤y ∧ y%4=0 := by
  have hm := second_stopping_affine_residual_mod_three j m k d y hgate hscale
  omega

#print axioms first_stopping_k_mod_three
#print axioms second_stopping_k_plus_two_mod_three
#print axioms second_stopping_not_power_of_two
#print axioms second_stopping_affine_residual_mod_three
#print axioms second_stopping_affine_residual_ge_four
end BB6.Agent29Depth
