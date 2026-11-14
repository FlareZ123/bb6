import TM63RootQ4Attainable
import Lean.Elab.Tactic.Omega

/-!
# Exact root-specific arithmetic at the seven-step middle boundary

The published first reset produces
  tm63Index1 = 31 * 2^A - 1,
where A is the first-section exponent.  This file proves from the existing
CostRecurrence lemmas that A is odd and at least five.  Consequently, after
the first seven decrements the actual root index is exactly 8*k, where
k = 31*2^(A-3)-1 is odd.  The marker after those seven decrements is 1.

These are arithmetic facts about the source itinerary parameters.  They do
not assert that the corresponding seven original-TM2 machine transitions
have been composed; that is a separate source-run obligation.
-/

namespace BB6Coverage.Agent42RootCountdown

open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable

private theorem pow2_ge_four (n : Nat) (hn : 2 ≤ n) : 4 ≤ 2^n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Nat.pow_add]
  norm_num
  have hp : 0 < 2^k := Nat.pow_pos (by decide)
  omega

private theorem nextRight_ge_two (b : Nat) (hb : 2 ≤ b) :
    2 ≤ nextRight b := by
  unfold nextRight
  have hp := pow2_ge_four b hb
  omega

private theorem sectionResult_right_ge_two
    (n m a b : Nat) (hb : 2 ≤ b) :
    2 ≤ (sectionResult n m a b).right := by
  induction n generalizing m a b with
  | zero =>
      simpa [sectionResult] using hb
  | succ n ih =>
      change 2 ≤
        (sectionResult n (nextMarker m) (nextExponent m a b)
          (nextRight b)).right
      exact ih (nextMarker m) (nextExponent m a b) (nextRight b)
        (nextRight_ge_two b hb)

/-- The first-section exponent A is at least five. -/
theorem tm63FirstSection_exponent_ge_five :
    5 ≤ tm63FirstSection.exponent := by
  have hmarker : (sectionResult 6 2 6 63).marker = 2 := by
    rw [sectionResult_marker]
    norm_num
  have hexponent :
      (sectionResult 7 2 6 63).exponent =
        (sectionResult 6 2 6 63).exponent +
          (sectionResult 6 2 6 63).right + 2 := by
    rw [sectionResult_exponent_snoc 6 2 6 63]
    rw [hmarker]
    simp [nextExponent]
  have ha : 0 < (sectionResult 6 2 6 63).exponent :=
    sectionResult_exponent_pos 6 2 6 63 (by decide)
  have hb : 2 ≤ (sectionResult 6 2 6 63).right :=
    sectionResult_right_ge_two 6 2 6 63 (by decide)
  change 5 ≤ (sectionResult 7 2 6 63).exponent
  rw [hexponent]
  omega

/-- The exact first-reset index, specialized only in its fixed length 3. -/
theorem tm63_index1_exact :
    tm63Index1 = 31 * 2^tm63FirstSection.exponent - 1 := by
  change resetIndex 3 tm63FirstSection.exponent = _
  unfold resetIndex
  norm_num

/-- The odd parameter reached after seven decrements of the genuine root. -/
def tm63RootMiddleK : Nat :=
  31 * 2^(tm63FirstSection.exponent - 3) - 1

private theorem tm63_first_exponent_pow_split :
    2^tm63FirstSection.exponent =
      8 * 2^(tm63FirstSection.exponent - 3) := by
  have hA := tm63FirstSection_exponent_ge_five
  rw [show tm63FirstSection.exponent =
      (tm63FirstSection.exponent - 3) + 3 by omega]
  rw [Nat.pow_add]
  norm_num
  omega

/-- Seven decrements leave an exact multiple of eight, not merely a
congruence class. -/
theorem tm63_index1_after_seven :
    tm63Index1 - 7 = 8 * tm63RootMiddleK := by
  have hA := tm63FirstSection_exponent_ge_five
  rw [tm63_index1_exact, tm63_first_exponent_pow_split]
  simp [tm63RootMiddleK]
  omega

/-- Equivalent form identifying the actual starting residue for the
first seven middle-section source transitions. -/
theorem tm63_index1_eq_8k7 :
    tm63Index1 = 8 * tm63RootMiddleK + 7 := by
  have h := tm63_index1_after_seven
  omega

/-- The parameter k at the seven-decrement boundary is odd. -/
theorem tm63_root_middle_k_odd :
    tm63RootMiddleK % 2 = 1 := by
  have hA : 5 ≤ tm63FirstSection.exponent :=
    tm63FirstSection_exponent_ge_five
  have hAodd : tm63FirstSection.exponent % 2 = 1 := by
    simpa [tm63FirstSection] using first_stage_exponent_odd
  have hpowEven :
      (2^(tm63FirstSection.exponent - 3)) % 2 = 0 := by
    have hpos : 0 < tm63FirstSection.exponent - 3 := by omega
    obtain ⟨t, ht⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show tm63FirstSection.exponent - 3 ≠ 0 by omega)
    rw [ht, Nat.pow_succ]
    simp
  have hprodEven :
      (31 * 2^(tm63FirstSection.exponent - 3)) % 2 = 0 := by
    simp [Nat.mul_mod, hpowEven]
  unfold tm63RootMiddleK
  omega

/-- The marker reached after seven decrements from the m=2 root is m=1. -/
theorem tm63_middle_seven_marker :
    (sectionResult 7 2 tm63FirstSection.exponent
      tm63FirstSection.right).marker = 1 := by
  rw [sectionResult_marker]
  norm_num

#print axioms tm63FirstSection_exponent_ge_five
#print axioms tm63_index1_exact
#print axioms tm63_index1_after_seven
#print axioms tm63_index1_eq_8k7
#print axioms tm63_root_middle_k_odd
#print axioms tm63_middle_seven_marker

end BB6Coverage.Agent42RootCountdown
