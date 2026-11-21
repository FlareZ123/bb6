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

/-- L source-carry formulas plus the correction hypotheses imply the 01,00,00 reset. -/
theorem left_source_derived_reset
    (K B xK1 yK C F py a b a1 b1 a2 b2 : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B)
    (hx0 : 0 ≤ xK1) (hx3 : xK1 < 3 * K)
    (hy0 : 0 ≤ yK) (hyK : yK < K)
    (hpy0 : 0 ≤ py) (hpy2 : py ≤ 2)
    (haDef : a = (xK1 - 3 * yK + C) / (3 * K))
    (hbDef : b = (3 * yK + F) / (3 * K))
    (ha1def : a1 = (a - py) / 3)
    (hb1def : b1 = (py + b) / 3)
    (ha2def : a2 = (a1 - 1) / 3)
    (hb2def : b2 = (1 + b1) / 3) :
    a2 / 3 = -1 ∧ b2 / 3 = 0 ∧
      NonMono ((a - py) % 3) ((a1 - 1) % 3) (a2 % 3) := by
  have hBounds := left_source_carry_bounds K B xK1 yK C F hK hBK hClo hChi hFlo hFhi hx0 hx3 hy0 hyK
  rcases hBounds with ⟨ha0, haHi, hb0, hbHi⟩
  have haLo : -2 ≤ a := by rw [haDef]; exact ha0
  have haUpper : a ≤ 1 := by rw [haDef]; exact haHi
  have hbLo : -1 ≤ b := by rw [hbDef]; exact hb0
  have hbUpper : b ≤ 1 := by rw [hbDef]; exact hbHi
  exact left_three_symbol_reset py a b a1 b1 a2 b2 hpy0 hpy2 haLo haUpper hbLo hbUpper ha1def hb1def ha2def hb2def

/-- R source-carry formulas plus the correction hypotheses imply the 01,00,00 reset. -/
theorem right_source_derived_reset
    (K B xK1 xK yK C F px py a b a1 b1 a2 b2 : Int)
    (hK : 0 < K) (hBK : B < K)
    (hClo : -B ≤ C) (hChi : C ≤ B)
    (hFlo : -B ≤ F) (hFhi : F ≤ B)
    (hx10 : 0 ≤ xK1) (hx13 : xK1 < 3 * K)
    (hx0 : 0 ≤ xK) (hxK : xK < K)
    (hy0 : 0 ≤ yK) (hyK : yK < K)
    (hpx0 : 0 ≤ px) (hpx2 : px ≤ 2)
    (hpy0 : 0 ≤ py) (hpy2 : py ≤ 2)
    (haDef : a = (-xK1 - 3 * xK - 3 * yK + C) / (3 * K))
    (hbDef : b = (3 * xK + 3 * yK + F) / (3 * K))
    (ha1def : a1 = (a - px - py) / 3)
    (hb1def : b1 = (px + py + b) / 3)
    (ha2def : a2 = (a1 - 1) / 3)
    (hb2def : b2 = (1 + b1) / 3) :
    a2 / 3 = -1 ∧ b2 / 3 = 0 ∧
      NonMono ((a - px - py) % 3) ((a1 - 1) % 3) (a2 % 3) := by
  have hBounds := right_source_carry_bounds K B xK1 xK yK C F hK hBK hClo hChi hFlo hFhi hx10 hx13 hx0 hxK hy0 hyK
  rcases hBounds with ⟨ha0, haHi, hb0, hbHi⟩
  have haLo : -4 ≤ a := by rw [haDef]; exact ha0
  have haUpper : a ≤ 0 := by rw [haDef]; exact haHi
  have hbLo : -1 ≤ b := by rw [hbDef]; exact hb0
  have hbUpper : b ≤ 2 := by rw [hbDef]; exact hbHi
  exact right_three_symbol_reset px py a b a1 b1 a2 b2 hpx0 hpx2 hpy0 hpy2 haLo haUpper hbLo hbUpper ha1def hb1def ha2def hb2def

/-- The four affine correction terms are bounded by the common mass buffer. -/
theorem correction_bounds_from_DR
    (ell D R cC cF : Int)
    (hDlo : -ell ≤ D) (hDhi : D ≤ ell)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell)
    (hcClo : -122 ≤ cC) (hcChi : cC ≤ 122)
    (hcFlo : -84 ≤ cF) (hcFhi : cF ≤ 84) :
    -(34 * ell + 122) ≤ -18 * D - 16 * R + cC ∧
      -18 * D - 16 * R + cC ≤ 34 * ell + 122 ∧
      -(34 * ell + 122) ≤ 12 * D + 12 * R + cF ∧
      12 * D + 12 * R + cF ≤ 34 * ell + 122 ∧
      -(34 * ell + 122) ≤ 12 * D + 4 * R + cC ∧
      12 * D + 4 * R + cC ≤ 34 * ell + 122 ∧
      -(34 * ell + 122) ≤ -6 * D + cF ∧
      -6 * D + cF ≤ 34 * ell + 122 := by
  omega

/-- Drain-count constraints imply the D,R bounds used by the correction estimate. -/
theorem drain_DR_bounds
    (ell L n1 n2 : Int)
    (hLell : L ≤ ell)
    (hn10 : 0 ≤ n1) (hn20 : 0 ≤ n2)
    (hnSum : n1 + n2 ≤ L) :
    -ell ≤ L - 2 * n2 ∧ L - 2 * n2 ≤ ell ∧
      0 ≤ n1 + n2 ∧ n1 + n2 ≤ ell := by
  omega

inductive SectorBranch where
  | LO_L | LE_L | RO_L | RE_L
  | LO_R | LE_R | RO_R | RE_R
  deriving DecidableEq

def sourceCorrectionC (s : SectorBranch) (D R : Int) : Int :=
  match s with
  | .LO_L => -18 * D - 16 * R - 122
  | .LE_L => -18 * D - 16 * R - 68
  | .RO_L => -18 * D - 16 * R
  | .RE_L => -18 * D - 16 * R - 36
  | .LO_R => 12 * D + 4 * R - 6
  | .LE_R => 12 * D + 4 * R - 12
  | .RO_R => 12 * D + 4 * R - 44
  | .RE_R => 12 * D + 4 * R - 20

def sourceCorrectionF (s : SectorBranch) (D R : Int) : Int :=
  match s with
  | .LO_L => 12 * D + 12 * R + 84
  | .LE_L => 12 * D + 12 * R + 48
  | .RO_L => 12 * D + 12 * R
  | .RE_L => 12 * D + 12 * R + 18
  | .LO_R => -6 * D + 24
  | .LE_R => -6 * D + 18
  | .RO_R => -6 * D + 30
  | .RE_R => -6 * D + 18

/-- The eight branch/sector correction constants satisfy |cC|≤122 and |cF|≤84. -/
theorem sector_correction_bounds
    (ell D R : Int) (s : SectorBranch)
    (hDlo : -ell ≤ D) (hDhi : D ≤ ell)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell) :
    -(34 * ell + 122) ≤ sourceCorrectionC s D R ∧
      sourceCorrectionC s D R ≤ 34 * ell + 122 ∧
      -(34 * ell + 122) ≤ sourceCorrectionF s D R ∧
      sourceCorrectionF s D R ≤ 34 * ell + 122 := by
  cases s <;> simp [sourceCorrectionC, sourceCorrectionF] <;> omega

/-- The mass-indexed drain inequalities are enough to supply the D,R hypotheses. -/
theorem source_correction_bounds_from_drain_counts
    (ell L n1 n2 : Int) (s : SectorBranch)
    (hLell : L ≤ ell)
    (hn10 : 0 ≤ n1) (hn20 : 0 ≤ n2)
    (hnSum : n1 + n2 ≤ L) :
    -(34 * ell + 122) ≤ sourceCorrectionC s (L - 2 * n2) (n1 + n2) ∧
      sourceCorrectionC s (L - 2 * n2) (n1 + n2) ≤ 34 * ell + 122 ∧
      -(34 * ell + 122) ≤ sourceCorrectionF s (L - 2 * n2) (n1 + n2) ∧
      sourceCorrectionF s (L - 2 * n2) (n1 + n2) ≤ 34 * ell + 122 := by
  have hDR := drain_DR_bounds ell L n1 n2 hLell hn10 hn20 hnSum
  exact sector_correction_bounds ell (L - 2 * n2) (n1 + n2) s hDR.1 hDR.2.1 hDR.2.2.1 hDR.2.2.2

end BB6.SourceDerivedReset
