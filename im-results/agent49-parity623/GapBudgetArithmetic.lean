import Std

namespace BB6.Agent49GapBudgetArithmetic

/-- The triangular sum of powers of three used by the evaluator. -/
def ternaryOnes (n : Nat) : Nat := (3^n - 1) / 2

theorem two_pow_le_three_pow (n : Nat) : 2^n ≤ 3^n :=
  Nat.pow_le_pow_left (by omega) n

/-- A coordinate x is covered by the ternary budget at its binary bit length
plus two. This is the arithmetic bridge used by the finite root scan. -/
theorem ternaryOnes_log2_bound (x : Nat) :
    x ≤ ternaryOnes (x.log2 + 3) := by
  by_cases hx0 : x = 0
  · simp [hx0, ternaryOnes]
  have hx : x < 2^(x.log2 + 1) := Nat.lt_log2_self
  have hpow2 : 2^(x.log2 + 3) = 4 * 2^(x.log2 + 1) := by
    rw [show x.log2 + 3 = (x.log2 + 1) + 2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hscale : 4*x < 2^(x.log2 + 3) := by
    calc
      4*x < 4 * 2^(x.log2 + 1) :=
        Nat.mul_lt_mul_of_pos_left hx (by omega)
      _ = 2^(x.log2 + 3) := hpow2.symm
  have hbound : 2*x + 1 ≤ 2^(x.log2 + 3) := by omega
  have hpow : 2^(x.log2 + 3) ≤ 3^(x.log2 + 3) :=
    two_pow_le_three_pow (x.log2 + 3)
  have hbig : 2*x + 1 ≤ 3^(x.log2 + 3) := by omega
  unfold ternaryOnes
  omega

/-- For positive x the same exponent gives a strict ternary budget, needed by
the even near-right sector's strict evaluator condition. -/
theorem ternaryOnes_log2_strict (x : Nat) (hx : 0 < x) :
    x < ternaryOnes (x.log2 + 3) := by
  by_cases hx1 : x = 1
  · subst x
    decide
  have hx2 : 2 ≤ x := by omega
  have hpow2 : 2^(x.log2 + 3) = 4 * 2^(x.log2 + 1) := by
    rw [show x.log2 + 3 = (x.log2 + 1) + 2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hxlog : x < 2^(x.log2 + 1) := Nat.lt_log2_self
  have hscale : 4*x < 2^(x.log2 + 3) := by
    calc
      4*x < 4 * 2^(x.log2 + 1) :=
        Nat.mul_lt_mul_of_pos_left hxlog (by omega)
      _ = 2^(x.log2 + 3) := hpow2.symm
  have hpow : 2^(x.log2 + 3) ≤ 3^(x.log2 + 3) :=
    two_pow_le_three_pow (x.log2 + 3)
  have hbig : 2*x + 3 ≤ 3^(x.log2 + 3) := by omega
  unfold ternaryOnes
  omega

theorem ternaryOnes_budget_of_bit_length (x k : Nat)
    (hk : x.log2 + 3 ≤ k) :
    x ≤ ternaryOnes k := by
  have hmono : 3^(x.log2 + 3) ≤ 3^k :=
    Nat.pow_le_pow_of_le (by omega) hk
  have hbase := ternaryOnes_log2_bound x
  unfold ternaryOnes at *
  omega

theorem ternaryOnes_strict_budget_of_bit_length (x k : Nat)
    (hx : 0 < x) (hk : x.log2 + 3 ≤ k) :
    x < ternaryOnes k := by
  have hmono : 3^(x.log2 + 3) ≤ 3^k :=
    Nat.pow_le_pow_of_le (by omega) hk
  have hbase := ternaryOnes_log2_strict x hx
  unfold ternaryOnes at *
  omega

#print axioms ternaryOnes_budget_of_bit_length
#print axioms ternaryOnes_strict_budget_of_bit_length

end BB6.Agent49GapBudgetArithmetic
