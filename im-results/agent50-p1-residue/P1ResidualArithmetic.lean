import Std

namespace BB6.Agent50P1

/-- The odd index in the complete three-branch inverse of a residual critical feeder. -/
def s (k : Nat) : Nat := 7 * 2^(16*k+7) - (2*k+3)

private theorem bound (k : Nat) : 16*k+8 ≤ 2^(16*k+7) := by
  have h := Nat.lt_pow_self (n:=16*k+7) (a:=2) (by decide)
  omega

private theorem bound2 (k : Nat) : 2*k+3 ≤ 7*2^(16*k+7) := by
  have h := bound k
  omega

private theorem s_add (k : Nat) : s k + 2*k+3 = 7*2^(16*k+7) := by
  have hb := bound2 k
  simp only [s]
  omega

/-- The critical odd-sector feeder is exactly (16*s(k)+12,3). -/
theorem target_shape (k : Nat) :
  14*2^(16*k+10)-2*(16*k+10)-16 = 16*s k+12 := by
  have hp : 2^(16*k+10) = 8*2^(16*k+7) := by
    have he : 16*k+10 = (16*k+7)+3 := by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have hs := s_add k
  rw [hp]
  omega

/-- The parameter s(k) is odd and at least 3. -/
theorem s_odd (k : Nat) : s k % 2 = 1 := by
  have hs := s_add k
  have hp : 2^(16*k+7) = 2*2^(16*k+6) := by
    have he : 16*k+7=(16*k+6)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  rw [hp] at hs
  omega

theorem s_ge_three (k : Nat) : 3 ≤ s k := by
  have hs := s_add k
  have hb := bound k
  omega

/-- Both candidate even-phase power values lie strictly between consecutive 14*2^j. -/
theorem critical_sandwich (k : Nat) :
    14*2^(16*k+9) < 11*s k+13 ∧
    11*s k+13 < 14*2^(16*k+10) ∧
    14*2^(16*k+9) < 13*s k+15 ∧
    13*s k+15 < 14*2^(16*k+10) := by
  have hs := s_add k
  have hb := bound k
  have h9 : 2^(16*k+9) = 4*2^(16*k+7) := by
    have he : 16*k+9 = (16*k+7)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have h10 : 2^(16*k+10) = 8*2^(16*k+7) := by
    have he : 16*k+10 = (16*k+7)+3 := by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  rw [h9,h10]
  omega

/-- Uniform no-power obstruction of both possible odd-input G branches. -/
theorem no_power_11 (k j : Nat) : 11*s k+13 ≠ 14*2^j := by
  obtain ⟨hl,hu,_,_⟩ := critical_sandwich k
  intro he
  by_cases hj : j<16*k+10
  · have hp : 2^j ≤ 2^(16*k+9) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp : 2^(16*k+10) ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem no_power_13 (k j : Nat) : 13*s k+15 ≠ 14*2^j := by
  obtain ⟨_,_,hl,hu⟩ := critical_sandwich k
  intro he
  by_cases hj : j<16*k+10
  · have hp : 2^j ≤ 2^(16*k+9) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp : 2^(16*k+10) ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

#print axioms target_shape
#print axioms s_odd
#print axioms s_ge_three
#print axioms critical_sandwich
#print axioms no_power_11
#print axioms no_power_13
end BB6.Agent50P1
