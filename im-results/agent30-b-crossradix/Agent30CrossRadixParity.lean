import Agent30CrossRadix

namespace BB6.Agent30Cross

theorem G_even_shift (z d : Nat) : G (z+2*d) = G z + 3*d := by
  unfold G
  omega

theorem iterG_two_adic_shift (n z d : Nat) :
    iterG n (z+2^n*d) = iterG n z + 3^n*d := by
  induction n generalizing z d with
  | zero => simp [iterG]
  | succ n ih =>
    change G (iterG n (z+2^(n+1)*d)) = G (iterG n z)+3^(n+1)*d
    have hpow : 2^(n+1)*d=2^n*(2*d) := by
      simp [Nat.pow_succ]
      ac_rfl
    rw [hpow, ih]
    have hmul : 3^n*(2*d)=2*(3^n*d) := by ac_rfl
    rw [hmul, G_even_shift]
    simp only [Nat.pow_succ]
    ac_rfl

/-- Within one output class modulo 3^n, both output parities occur. -/
theorem residue_parity_ambiguous (n z : Nat) :
    (iterG n (z+2^n)) % 3^n = (iterG n z) % 3^n ∧
    (iterG n (z+2^n)) % 2 ≠ (iterG n z) % 2 := by
  have hh : iterG n (z+2^n) = iterG n z + 3^n := by
    simpa only [Nat.mul_one] using iterG_two_adic_shift n z 1
  constructor
  · rw [hh]
    simp
  · rw [hh]
    have hp : 3^n % 2 = 1 := by
      simp [Nat.pow_mod]
    have hbit : (iterG n z)%2<2 := Nat.mod_lt _ (by decide)
    rw [Nat.add_mod,hp]
    omega

#print axioms iterG_two_adic_shift
#print axioms residue_parity_ambiguous
end BB6.Agent30Cross
