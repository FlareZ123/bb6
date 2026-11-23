import Lean

namespace BB6TerminalSyncBarrier

theorem left_small_residual_quotient
    (P Qx Qy rx ry Z : Int)
    (hP : 0 < P)
    (hrx0 : 0 ≤ rx) (hrxP : rx < P)
    (hry0 : 0 ≤ ry) (hryP : ry < P)
    (hZlo : -P < Z) (hZhi : Z < P)
    (hdecomp : Z = P * (Qx - 3 * Qy) + (rx - 3 * ry)) :
    -1 ≤ Qx - 3 * Qy ∧ Qx - 3 * Qy ≤ 3 := by
  let q := Qx - 3 * Qy
  have hP0 : 0 ≤ P := by omega
  have heLo : -3 * P < rx - 3 * ry := by omega
  have heHi : rx - 3 * ry < P := by omega
  constructor
  · by_cases hq : -1 ≤ q
    · simpa [q] using hq
    · have hq2 : q ≤ -2 := by omega
      have hmul : P * q ≤ P * (-2) := Int.mul_le_mul_of_nonneg_left hq2 hP0
      have hmul' : P * (Qx - 3 * Qy) ≤ P * (-2) := by simpa [q] using hmul
      have hz : Z < -P := by omega
      omega
  · by_cases hq : q ≤ 3
    · simpa [q] using hq
    · have hq4 : 4 ≤ q := by omega
      have hmul : P * 4 ≤ P * q := Int.mul_le_mul_of_nonneg_left hq4 hP0
      have hmul' : P * 4 ≤ P * (Qx - 3 * Qy) := by simpa [q] using hmul
      have hz : P < Z := by omega
      omega

theorem right_small_residual_quotient
    (P Qx Qy rx ry Z : Int)
    (hP : 0 < P)
    (hrx0 : 0 ≤ rx) (hrxP : rx < P)
    (hry0 : 0 ≤ ry) (hryP : ry < P)
    (hZlo : -P < Z) (hZhi : Z < P)
    (hdecomp : Z = P * (4 * Qx + 3 * Qy) + (4 * rx + 3 * ry)) :
    -7 ≤ 4 * Qx + 3 * Qy ∧ 4 * Qx + 3 * Qy ≤ 0 := by
  let q := 4 * Qx + 3 * Qy
  have hP0 : 0 ≤ P := by omega
  have heLo : 0 ≤ 4 * rx + 3 * ry := by omega
  have heHi : 4 * rx + 3 * ry < 7 * P := by omega
  constructor
  · by_cases hq : -7 ≤ q
    · simpa [q] using hq
    · have hq8 : q ≤ -8 := by omega
      have hmul : P * q ≤ P * (-8) := Int.mul_le_mul_of_nonneg_left hq8 hP0
      have hmul' : P * (4 * Qx + 3 * Qy) ≤ P * (-8) := by simpa [q] using hmul
      have hz : Z < -P := by omega
      omega
  · by_cases hq : q ≤ 0
    · simpa [q] using hq
    · have hq1 : 1 ≤ q := by omega
      have hmul : P * 1 ≤ P * q := Int.mul_le_mul_of_nonneg_left hq1 hP0
      have hmul' : P * 1 ≤ P * (4 * Qx + 3 * Qy) := by simpa [q] using hmul
      have hz : P ≤ Z := by omega
      omega

end BB6TerminalSyncBarrier
