import Agent30CrossRadix

namespace BB6.Agent30Cross

/-- An exact weighted record of the n observed scalar parity bits. -/
def wordWeight : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, z => 3 * wordWeight n z + 2^n * (8 + 7 * (iterG n z % 2))

theorem G_double (z : Nat) : 2*G z = 3*z + 8 + 7*(z%2) := by
  unfold G
  omega

/-- All finite orbit outputs have an exact weighted parity-word formula. -/
theorem wordWeight_exact (n z : Nat) :
    2^n * iterG n z = 3^n * z + wordWeight n z := by
  induction n with
  | zero => simp [iterG, wordWeight]
  | succ n ih =>
    calc
      2^(n+1)*iterG (n+1) z = 2^n * (2 * G (iterG n z)) := by
        simp only [Nat.pow_succ, iterG]
        ac_rfl
      _ = 2^n * (3 * iterG n z + 8 + 7 * (iterG n z % 2)) := by
        rw [G_double]
      _ = 3 * (2^n * iterG n z) + 2^n * (8 + 7 * (iterG n z % 2)) := by
        simp only [Nat.mul_add]
        ac_rfl
      _ = 3 * (3^n * z + wordWeight n z) + 2^n * (8 + 7 * (iterG n z % 2)) := by
        rw [ih]
      _ = 3^(n+1)*z + wordWeight (n+1) z := by
        simp only [wordWeight, Nat.pow_succ, Nat.mul_add]
        ac_rfl

theorem wordWeight_residue (n z : Nat) :
    (2^n * iterG n z) % 3^n = wordWeight n z % 3^n := by
  have h := wordWeight_exact n z
  rw [h, Nat.add_mod]
  have hz : (3^n*z) % 3^n = 0 := by simp
  rw [hz]
  simp

#print axioms G_double
#print axioms wordWeight_exact
#print axioms wordWeight_residue
end BB6.Agent30Cross
