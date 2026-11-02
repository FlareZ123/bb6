import BMod7Core
namespace BB6.OneDim

theorem five_power_nonzero_mod7 (n : Nat) : (5^n)%7 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpos : 0 < (5^n)%7 := by omega
      have hlt : (5^n)%7 < 7 := Nat.mod_lt _ (by decide)
      rw [Nat.pow_succ]
      have hmod : (5^n * 5)%7 = ((5^n)%7*5)%7 := by
        rw [Nat.mul_mod]
      rw [hmod]
      omega

/-- The actual z=0 scalar orbit never visits residue six modulo seven. -/
theorem iterG_zero_ne_six_mod7 (n : Nat) : (iterG n 0)%7 ≠ 6 := by
  have h := iterG_zero_mod7 n
  have hn := five_power_nonzero_mod7 n
  omega

#print axioms iterG_zero_ne_six_mod7
end BB6.OneDim
