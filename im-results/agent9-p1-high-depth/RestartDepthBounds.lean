import Lean.Elab.Tactic.Omega
set_option maxRecDepth 8192

namespace BB6.Agent9RestartDepthBounds

/-- Source-parent inequalities under the cost-one terminal bound.
Here M=m0+n, q=bp/2, d=dp, D=d0-1, X=2^t D=dp+bp/2+3,
and AP is the restart defect coefficient times P. -/
theorem cost_one_parent_bounds
    (P M t d q X D AP : Nat)
    (hcap : 128 * (M + 3) < 93 * P)
    (hD0 : 49 * D + 14 * M = AP + 6)
    (hmass : d + 2 * q + 2 * M + 11 = 14 * P + 2 * t)
    (hX : X = d + q + 3)
    (hM : t + 1 ≤ M) :
    128 * X > 803 * P + 128 * (t + 1) ∧
    X < 14 * P ∧
    49 * D ≤ AP + 6 ∧
    3136 * D + 651 * P > 64 * AP + 3072 := by
  have hXrel : 14 * P + 2 * t ≤ 2 * X + 2 * M + 4 := by omega
  have hXlo : 128 * X > 803 * P + 128 * (t + 1) := by omega
  have hXupper : X + 2 * M + 8 ≤ 14 * P + 2 * t := by omega
  have hXhi : X < 14 * P := by omega
  have hDupper : 49 * D ≤ AP + 6 := by omega
  have hDrel : 3136 * D + 896 * M = 64 * AP + 384 := by omega
  have hcap' : 896 * M + 2688 < 651 * P := by omega
  have hDlower : 3136 * D + 651 * P > 64 * AP + 3072 := by omega
  exact ⟨hXlo,hXhi,hDupper,hDlower⟩

/-- Source-parent inequalities under the cost-two terminal bound. -/
theorem cost_two_parent_bounds
    (P M t d q X D AP : Nat)
    (hcap : 256 * (M + 3) < 77 * P)
    (hD0 : 49 * D + 14 * M = AP + 6)
    (hmass : d + 2 * q + 2 * M + 11 = 14 * P + 2 * t)
    (hX : X = d + q + 3)
    (hM : t + 1 ≤ M) :
    256 * X > 1715 * P + 256 * (t + 1) ∧
    X < 14 * P ∧
    49 * D ≤ AP + 6 ∧
    6272 * D + 539 * P > 128 * AP + 6144 := by
  have hXrel : 14 * P + 2 * t ≤ 2 * X + 2 * M + 4 := by omega
  have hXlo : 256 * X > 1715 * P + 256 * (t + 1) := by omega
  have hXupper : X + 2 * M + 8 ≤ 14 * P + 2 * t := by omega
  have hXhi : X < 14 * P := by omega
  have hDupper : 49 * D ≤ AP + 6 := by omega
  have hDrel : 6272 * D + 1792 * M = 128 * AP + 768 := by omega
  have hcap' : 1792 * M + 5376 < 539 * P := by omega
  have hDlower : 6272 * D + 539 * P > 128 * AP + 6144 := by omega
  exact ⟨hXlo,hXhi,hDupper,hDlower⟩

theorem cost_one_I20_depth
    (P X D t : Nat)
    (hP : 2^83 ≤ P)
    (hXlo : 128 * X > 803 * P + 128 * (t + 1))
    (hXhi : X < 14 * P)
    (hDupper : 49 * D ≤ 18 * P + 6)
    (hDlower : 3136 * D + 651 * P > 1152 * P + 3072)
    (hX : X = 2^t * D) : t = 5 ∨ t = 6 := by
  have htLower : 5 ≤ t := by
    by_cases hlt : t < 5
    · have hpow : 2^t ≤ 16 := by
        calc
          2^t ≤ 2^4 := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
          _ = 16 := by decide
      have hXupper : 49 * 128 * X ≤ 2048 * (18 * P + 6) := by
        rw [hX]
        calc
          49 * 128 * (2^t * D) ≤ 49 * 128 * (16 * D) := by
            exact Nat.mul_le_mul_left (49 * 128) (Nat.mul_le_mul_right D hpow)
          _ = 2048 * (49 * D) := by omega
          _ ≤ 2048 * (18 * P + 6) := Nat.mul_le_mul_left 2048 hDupper
      have hXlower : 49 * 803 * P < 49 * 128 * X := by omega
      omega
    · omega
  have htUpper : t ≤ 6 := by
    by_cases hgt : 6 < t
    · have hpow : 128 ≤ 2^t := by
        calc
          128 = 2^7 := by decide
          _ ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
      have hDlower' : 3136 * D > 501 * P + 3072 := by omega
      have hXlower : 128 * (501 * P + 3072) < 3136 * X := by
        rw [hX]
        calc
          128 * (501 * P + 3072) < 128 * (3136 * D) := Nat.mul_lt_mul_of_pos_left hDlower' (by decide)
          _ = 3136 * (128 * D) := by omega
          _ ≤ 3136 * (2^t * D) := Nat.mul_le_mul_left 3136 (Nat.mul_le_mul_right D hpow)
      have hXupper : 3136 * X < 3136 * (14 * P) := by omega
      omega
    · omega
  omega

theorem cost_one_I48_depth_lower
    (P X D t : Nat)
    (hP : 2^83 ≤ P)
    (hXlo : 128 * X > 803 * P + 128 * (t + 1))
    (hDupper : 49 * D ≤ 2 * P + 6)
    (hX : X = 2^t * D) : 8 ≤ t := by
  by_cases hlt : t < 8
  · have hpow : 2^t ≤ 128 := by
      calc
        2^t ≤ 2^7 := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
        _ = 128 := by decide
    have hXupper : 49 * 128 * X ≤ 16384 * (2 * P + 6) := by
      rw [hX]
      calc
        49 * 128 * (2^t * D) ≤ 49 * 128 * (128 * D) := by
          exact Nat.mul_le_mul_left (49 * 128) (Nat.mul_le_mul_right D hpow)
      _ = 16384 * (49 * D) := by omega
      _ ≤ 16384 * (2 * P + 6) := Nat.mul_le_mul_left 16384 hDupper
    have hXlower : 49 * 803 * P < 49 * 128 * X := by omega
    omega
  · omega

theorem cost_two_I20_depth
    (P X D t : Nat)
    (hP : 2^83 ≤ P)
    (hXlo : 256 * X > 1715 * P + 256 * (t + 1))
    (hXhi : X < 14 * P)
    (hDupper : 49 * D ≤ 18 * P + 6)
    (hDlower : 6272 * D + 539 * P > 2304 * P + 6144)
    (hX : X = 2^t * D) : t = 5 := by
  have htLower : 5 ≤ t := by
    by_cases hlt : t < 5
    · have hpow : 2^t ≤ 16 := by
        calc
          2^t ≤ 2^4 := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
          _ = 16 := by decide
      have hXupper : 49 * 256 * X ≤ 4096 * (18 * P + 6) := by
        rw [hX]
        calc
          49 * 256 * (2^t * D) ≤ 49 * 256 * (16 * D) := by
            exact Nat.mul_le_mul_left (49 * 256) (Nat.mul_le_mul_right D hpow)
          _ = 4096 * (49 * D) := by omega
          _ ≤ 4096 * (18 * P + 6) := Nat.mul_le_mul_left 4096 hDupper
      have hXlower : 49 * 1715 * P < 49 * 256 * X := by omega
      omega
    · omega
  have htUpper : t ≤ 5 := by
    by_cases hgt : 5 < t
    · have hpow : 64 ≤ 2^t := by
        calc
          64 = 2^6 := by decide
          _ ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
      have hDlower' : 6272 * D > 1765 * P + 6144 := by omega
      have hXlower : 64 * (1765 * P + 6144) < 6272 * X := by
        rw [hX]
        calc
          64 * (1765 * P + 6144) < 64 * (6272 * D) := Nat.mul_lt_mul_of_pos_left hDlower' (by decide)
          _ = 6272 * (64 * D) := by omega
          _ ≤ 6272 * (2^t * D) := Nat.mul_le_mul_left 6272 (Nat.mul_le_mul_right D hpow)
      have hXupper : 6272 * X < 6272 * (14 * P) := by omega
      omega
    · omega
  omega

theorem cost_two_I48_depth_lower
    (P X D t : Nat)
    (hP : 2^83 ≤ P)
    (hXlo : 256 * X > 1715 * P + 256 * (t + 1))
    (hDupper : 49 * D ≤ 2 * P + 6)
    (hX : X = 2^t * D) : 8 ≤ t := by
  by_cases hlt : t < 8
  · have hpow : 2^t ≤ 128 := by
      calc
        2^t ≤ 2^7 := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
        _ = 128 := by decide
    have hXupper : 49 * 256 * X ≤ 32768 * (2 * P + 6) := by
      rw [hX]
      calc
        49 * 256 * (2^t * D) ≤ 49 * 256 * (128 * D) := by
          exact Nat.mul_le_mul_left (49 * 256) (Nat.mul_le_mul_right D hpow)
      _ = 32768 * (49 * D) := by omega
      _ ≤ 32768 * (2 * P + 6) := Nat.mul_le_mul_left 32768 hDupper
    have hXlower : 49 * 1715 * P < 49 * 256 * X := by omega
    omega
  · omega

/-- Raw parent-coordinate versions: the exact source mass and inverse equations
are represented by hD0, hmass, hX, hM, and hpow. -/
theorem source_cost_one_I20_depth
    (P M t d q X D : Nat)
    (hP : 2^83 ≤ P)
    (hcap : 128 * (M + 3) < 93 * P)
    (hD0 : 49 * D + 14 * M = 18 * P + 6)
    (hmass : d + 2 * q + 2 * M + 11 = 14 * P + 2 * t)
    (hX : X = d + q + 3)
    (hM : t + 1 ≤ M)
    (hpow : X = 2^t * D) : t = 5 ∨ t = 6 := by
  have hb := cost_one_parent_bounds P M t d q X D (18 * P) hcap hD0 hmass hX hM
  rcases hb with ⟨hXlo,hXhi,hDupper,hDlower⟩
  have hDlower' : 3136 * D + 651 * P > 1152 * P + 3072 := by omega
  exact cost_one_I20_depth P X D t hP hXlo hXhi hDupper hDlower' hpow

theorem source_cost_one_I48_depth_lower
    (P M t d q X D : Nat)
    (hP : 2^83 ≤ P)
    (hcap : 128 * (M + 3) < 93 * P)
    (hD0 : 49 * D + 14 * M = 2 * P + 6)
    (hmass : d + 2 * q + 2 * M + 11 = 14 * P + 2 * t)
    (hX : X = d + q + 3)
    (hM : t + 1 ≤ M)
    (hpow : X = 2^t * D) : 8 ≤ t := by
  have hb := cost_one_parent_bounds P M t d q X D (2 * P) hcap hD0 hmass hX hM
  rcases hb with ⟨hXlo,hXhi,hDupper,hDlower⟩
  exact cost_one_I48_depth_lower P X D t hP hXlo hDupper hpow

theorem source_cost_two_I20_depth
    (P M t d q X D : Nat)
    (hP : 2^83 ≤ P)
    (hcap : 256 * (M + 3) < 77 * P)
    (hD0 : 49 * D + 14 * M = 18 * P + 6)
    (hmass : d + 2 * q + 2 * M + 11 = 14 * P + 2 * t)
    (hX : X = d + q + 3)
    (hM : t + 1 ≤ M)
    (hpow : X = 2^t * D) : t = 5 := by
  have hb := cost_two_parent_bounds P M t d q X D (18 * P) hcap hD0 hmass hX hM
  rcases hb with ⟨hXlo,hXhi,hDupper,hDlower⟩
  have hDlower' : 6272 * D + 539 * P > 2304 * P + 6144 := by omega
  exact cost_two_I20_depth P X D t hP hXlo hXhi hDupper hDlower' hpow

theorem source_cost_two_I48_depth_lower
    (P M t d q X D : Nat)
    (hP : 2^83 ≤ P)
    (hcap : 256 * (M + 3) < 77 * P)
    (hD0 : 49 * D + 14 * M = 2 * P + 6)
    (hmass : d + 2 * q + 2 * M + 11 = 14 * P + 2 * t)
    (hX : X = d + q + 3)
    (hM : t + 1 ≤ M)
    (hpow : X = 2^t * D) : 8 ≤ t := by
  have hb := cost_two_parent_bounds P M t d q X D (2 * P) hcap hD0 hmass hX hM
  rcases hb with ⟨hXlo,hXhi,hDupper,hDlower⟩
  exact cost_two_I48_depth_lower P X D t hP hXlo hDupper hpow

#print axioms cost_one_parent_bounds
#print axioms cost_two_parent_bounds
#print axioms source_cost_one_I20_depth
#print axioms source_cost_one_I48_depth_lower
#print axioms source_cost_two_I20_depth
#print axioms source_cost_two_I48_depth_lower

end BB6.Agent9RestartDepthBounds


namespace BB6.Agent9RestartDepthBounds.Offset

/-- The source affine energy plus the parent mass equation gives
I = 7(b-6d)+146. These lemmas convert the residual energies to
exact coordinate relations without subtraction in Nat. -/
theorem Is20_coordinate
    (b d : Nat) (h : 7 * b + 146 = 20 + 42 * d) : b + 18 = 6 * d := by
  omega

theorem Is48_coordinate
    (b d : Nat) (h : 7 * b + 146 = 48 + 42 * d) : b + 14 = 6 * d := by
  omega

theorem first_offset_mod7_I20
    (P M s b d T : Nat)
    (hV : b + 18 = 6 * d)
    (hmass : b + d + 2 * (M + 3 * s) + 13 = 14 * P)
    (hT : T = M + 6 + 3 * s) : T % 7 = 5 := by
  omega

theorem first_offset_mod7_I48
    (P M s b d T : Nat)
    (hV : b + 14 = 6 * d)
    (hmass : b + d + 2 * (M + 3 * s) + 13 = 14 * P)
    (hT : T = M + 6 + 3 * s) : T % 7 = 3 := by
  omega

theorem first_offset_mod14_I20
    (P M s b d T : Nat)
    (hV : b + 18 = 6 * d)
    (hmass : b + d + 2 * (M + 3 * s) + 13 = 14 * P)
    (hT : T = M + 6 + 3 * s)
    (hOdd : T % 2 = 1) : T % 14 = 5 := by
  omega

theorem first_offset_mod14_I48_even
    (P M s b d T : Nat)
    (hV : b + 14 = 6 * d)
    (hmass : b + d + 2 * (M + 3 * s) + 13 = 14 * P)
    (hT : T = M + 6 + 3 * s)
    (hEven : T % 2 = 0) : T % 14 = 10 := by
  omega

theorem first_offset_mod14_I48_odd
    (P M s b d T : Nat)
    (hV : b + 14 = 6 * d)
    (hmass : b + d + 2 * (M + 3 * s) + 13 = 14 * P)
    (hT : T = M + 6 + 3 * s)
    (hOdd : T % 2 = 1) : T % 14 = 3 := by
  omega

#print axioms Is20_coordinate
#print axioms Is48_coordinate
#print axioms first_offset_mod7_I20
#print axioms first_offset_mod7_I48
#print axioms first_offset_mod14_I20
#print axioms first_offset_mod14_I48_even
#print axioms first_offset_mod14_I48_odd

end BB6.Agent9RestartDepthBounds.Offset
