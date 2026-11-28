import ChampionScoreLowerBound
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ChampionPow1024

open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

/-!
Uniform-sized symbolic lower bound extracted from the SECOND source-counted
increment of the exact attained champion. The proof never evaluates
4^(2^63-1) or the giant champion score.
-/

private def secondRight : Nat := 2^63-1

private theorem second_increment_general (b : Nat)
    (h64 : 64 ≤ b) (h1024 : 1024 ≤ b) (hsmall : 9*b ≤ 2^128) :
    2^1024 ≤ proposedIncrementCost 1 6 71 b := by
  have hpow : 2^1024 ≤ 4^b := by
    calc
      2^1024 ≤ 4^1024 := Nat.pow_le_pow_left (by decide) _
      _ ≤ 4^b :=
        Nat.pow_le_pow_right (by decide) h1024
  have hb : 9*b ≤ 4^b := by
    calc
      9*b ≤ 2^128 := hsmall
      _ = 4^64 := by decide
      _ ≤ 4^b := Nat.pow_le_pow_right (by decide) h64
  unfold proposedIncrementCost
  omega

theorem second_increment_ge_pow1024 :
    2^1024 ≤ proposedIncrementCost 1 6 71 secondRight := by
  exact second_increment_general secondRight
    (by decide) (by decide) (by decide)

theorem second_increment_le_first_section :
    proposedIncrementCost 1 6 71 secondRight ≤
      (sectionResult 7 2 6 63).cost := by
  have hr : proposedIncrementCost 1 6 71 secondRight ≤
      (sectionResult 6 1 71 secondRight).cost := by
    simpa using
      (BB6.Agent38ChampionThreshold.sectionResult_firstCost_le
        5 1 71 secondRight)
  have hstep :
      (sectionResult 7 2 6 63).cost =
        proposedIncrementCost 2 7 6 63 +
        (sectionResult 6 1 71 secondRight).cost := by
    rfl
  rw [hstep]
  omega

theorem champion_score_ge_pow1024 :
    2^1024 ≤ proposedTM63Moves + 7 := by
  calc
    2^1024 ≤ proposedIncrementCost 1 6 71 secondRight :=
      second_increment_ge_pow1024
    _ ≤ (sectionResult 7 2 6 63).cost :=
      second_increment_le_first_section
    _ ≤ proposedTM63Moves + 7 :=
      BB6.Agent38ChampionThreshold.first_section_cost_le_champion_score

#print axioms second_increment_ge_pow1024
#print axioms second_increment_le_first_section
#print axioms champion_score_ge_pow1024

end BB6.Agent3ChampionPow1024
