import Lean

namespace BB6.SourceDerivedReset

def NonMono (u v w : Int) : Prop :=
  (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
  (u ≠ 2 ∨ v ≠ 2 ∨ w ≠ 2)

/-- L branch: the word 01,00,00 resets every source-derived L start. -/
theorem left_three_symbol_reset
    (py a b a1 b1 a2 b2 : Int)
    (hpy0 : 0 ≤ py) (hpy2 : py ≤ 2)
    (ha0 : -2 ≤ a) (ha1 : a ≤ 1)
    (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (ha1def : a1 = (a - py) / 3)
    (hb1def : b1 = (py + b) / 3)
    (ha2def : a2 = (a1 - 1) / 3)
    (hb2def : b2 = (1 + b1) / 3) :
    a2 / 3 = -1 ∧ b2 / 3 = 0 ∧
      NonMono ((a - py) % 3) ((a1 - 1) % 3) (a2 % 3) := by
  have ha1range : -2 ≤ a1 ∧ a1 ≤ 0 := by rw [ha1def]; omega
  have hb1range : -1 ≤ b1 ∧ b1 ≤ 1 := by rw [hb1def]; omega
  have ha2value : a2 = -1 := by rw [ha2def]; omega
  have hb2value : b2 = 0 := by rw [hb2def]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ha2value]
    omega
  · rw [hb2value]
    omega
  · change (((a - py) % 3 ≠ 0 ∨ (a1 - 1) % 3 ≠ 0 ∨ a2 % 3 ≠ 0) ∧
      ((a - py) % 3 ≠ 2 ∨ (a1 - 1) % 3 ≠ 2 ∨ a2 % 3 ≠ 2))
    constructor <;> omega

/-- R branch: the word 01,00,00 resets every source-derived R start. -/
theorem right_three_symbol_reset
    (px py a b a1 b1 a2 b2 : Int)
    (hpx0 : 0 ≤ px) (hpx2 : px ≤ 2)
    (hpy0 : 0 ≤ py) (hpy2 : py ≤ 2)
    (ha0 : -4 ≤ a) (ha1 : a ≤ 0)
    (hb0 : -1 ≤ b) (hb1 : b ≤ 2)
    (ha1def : a1 = (a - px - py) / 3)
    (hb1def : b1 = (px + py + b) / 3)
    (ha2def : a2 = (a1 - 1) / 3)
    (hb2def : b2 = (1 + b1) / 3) :
    a2 / 3 = -1 ∧ b2 / 3 = 0 ∧
      NonMono ((a - px - py) % 3) ((a1 - 1) % 3) (a2 % 3) := by
  have ha1range : -3 ≤ a1 ∧ a1 ≤ 0 := by rw [ha1def]; omega
  have hb1range : -1 ≤ b1 ∧ b1 ≤ 2 := by rw [hb1def]; omega
  have ha2range : -2 ≤ a2 ∧ a2 ≤ -1 := by rw [ha2def]; omega
  have hb2range : 0 ≤ b2 ∧ b2 ≤ 1 := by rw [hb2def]; omega
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · change (((a - px - py) % 3 ≠ 0 ∨ (a1 - 1) % 3 ≠ 0 ∨ a2 % 3 ≠ 0) ∧
      ((a - px - py) % 3 ≠ 2 ∨ (a1 - 1) % 3 ≠ 2 ∨ a2 % 3 ≠ 2))
    constructor <;> omega

/-- Arithmetic source-carry bounds for the L branch, assuming the correction bound B<K. -/
theorem left_source_carry_bounds
    (K B xK1 yK C F : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B)
    (hx0 : 0 ≤ xK1) (hx3 : xK1 < 3 * K)
    (hy0 : 0 ≤ yK) (hyK : yK < K) :
    -2 ≤ (xK1 - 3 * yK + C) / (3 * K) ∧
      (xK1 - 3 * yK + C) / (3 * K) ≤ 1 ∧
      -1 ≤ (3 * yK + F) / (3 * K) ∧
      (3 * yK + F) / (3 * K) ≤ 1 := by
  have hden : 0 < 3 * K := by omega
  have hn0lo : -4 * K + 3 ≤ xK1 - 3 * yK + C := by omega
  have hn0hi : xK1 - 3 * yK + C ≤ 4 * K - 1 := by omega
  have hn1lo : -K ≤ 3 * yK + F := by omega
  have hn1hi : 3 * yK + F ≤ 4 * K - 3 := by omega
  constructor
  · apply (Int.le_ediv_iff_mul_le hden).2
    omega
  constructor
  · apply (Int.ediv_le_iff_le_mul hden).2
    omega
  constructor
  · apply (Int.le_ediv_iff_mul_le hden).2
    omega
  · apply (Int.ediv_le_iff_le_mul hden).2
    omega

/-- Arithmetic source-carry bounds for the R branch, assuming the correction bound B<K. -/
theorem right_source_carry_bounds
    (K B xK1 xK yK C F : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B)
    (hx10 : 0 ≤ xK1) (hx13 : xK1 < 3 * K)
    (hx0 : 0 ≤ xK) (hxK : xK < K)
    (hy0 : 0 ≤ yK) (hyK : yK < K) :
    -4 ≤ (-xK1 - 3 * xK - 3 * yK + C) / (3 * K) ∧
      (-xK1 - 3 * xK - 3 * yK + C) / (3 * K) ≤ 0 ∧
      -1 ≤ (3 * xK + 3 * yK + F) / (3 * K) ∧
      (3 * xK + 3 * yK + F) / (3 * K) ≤ 2 := by
  have hden : 0 < 3 * K := by omega
  have hn0lo : -10 * K + 7 ≤ -xK1 - 3 * xK - 3 * yK + C := by omega
  have hn0hi : -xK1 - 3 * xK - 3 * yK + C ≤ K := by omega
  have hn1lo : -K ≤ 3 * xK + 3 * yK + F := by omega
  have hn1hi : 3 * xK + 3 * yK + F ≤ 7 * K - 6 := by omega
  constructor
  · apply (Int.le_ediv_iff_mul_le hden).2
    omega
  constructor
  · apply (Int.ediv_le_iff_le_mul hden).2
    omega
  constructor
  · apply (Int.le_ediv_iff_mul_le hden).2
    omega
  · apply (Int.ediv_le_iff_le_mul hden).2
    omega

end BB6.SourceDerivedReset
