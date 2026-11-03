import Init.Omega

namespace BB6.Agent9Cost

/-- A purely arithmetical bootstrap: dyadic inverse mass growth and a
narrow-left necessary condition force almost 16q prior inverse cost. -/
theorem logarithmic_cost_lower
    (q m r b : Nat)
    (hq : 1 ≤ q)
    (hr : q ≤ 2 ^ r)
    (hdyadic : 27 * 2 ^ (16 * q) ≤ 2 ^ m * (b + 12))
    (hnarrow : b ≤ 4 * m + 192 * q + 40) :
    16 * q ≤ m + r + 4 := by
  by_cases hgoal : 16 * q ≤ m + r + 4
  · exact hgoal
  ·
    have hexp : m + r + 9 ≤ 16 * q + 4 := by omega
    have hm : m ≤ 16 * q := by omega
    have hb : b + 12 ≤ 256 * q + 52 := by omega
    have hbound : b + 12 ≤ 2 ^ (r + 9) := by
      calc
        b + 12 ≤ 256 * q + 52 := hb
        _ ≤ 512 * q := by omega
        _ ≤ 512 * 2 ^ r := Nat.mul_le_mul_left 512 hr
        _ = 2 ^ (r + 9) := by simp [Nat.pow_add, Nat.mul_comm]
    have hpow : 2 ^ (m + r + 9) ≤ 2 ^ (16 * q + 4) :=
      Nat.pow_le_pow_right (by omega) hexp
    have hconflict : 27 * 2 ^ (16 * q) ≤ 16 * 2 ^ (16 * q) := by
      calc
        27 * 2 ^ (16 * q) ≤ 2 ^ m * (b + 12) := hdyadic
        _ ≤ 2 ^ m * 2 ^ (r + 9) := Nat.mul_le_mul_left (2 ^ m) hbound
        _ = 2 ^ (m + r + 9) := by simp [Nat.pow_add, Nat.add_assoc]
        _ ≤ 2 ^ (16 * q + 4) := hpow
        _ = 16 * 2 ^ (16 * q) := by simp [Nat.pow_add, Nat.mul_comm]
    have hp : 0 < 2 ^ (16 * q) := Nat.two_pow_pos _
    omega

/-- Binary-logarithmic form of the universal inverse cost barrier. -/
theorem logarithmic_cost_log2
    (q m b : Nat)
    (hq : 1 ≤ q)
    (hdyadic : 27 * 2 ^ (16 * q) ≤ 2 ^ m * (b + 12))
    (hnarrow : b ≤ 4 * m + 192 * q + 40) :
    16 * q ≤ m + Nat.log2 q + 5 := by
  have hqr : q ≤ 2 ^ (Nat.log2 q + 1) :=
    Nat.le_of_lt (Nat.lt_log2_self)
  have h := logarithmic_cost_lower q m (Nat.log2 q + 1) b
    hq hqr hdyadic hnarrow
  omega

#print axioms BB6.Agent9Cost.logarithmic_cost_log2

#print axioms BB6.Agent9Cost.logarithmic_cost_lower

end BB6.Agent9Cost
