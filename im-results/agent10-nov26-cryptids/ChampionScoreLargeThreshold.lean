import ChampionScoreLowerBound

namespace BB6.Agent10LargeThreshold

open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot
open BB6.Agent38ChampionThreshold

private theorem le_pow_two (b : Nat) : b ≤ 2^b := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [Nat.pow_succ]
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    omega

theorem increment_ge_pow (m n a b : Nat) :
    2^b ≤ proposedIncrementCost m n a b := by
  have hb := le_pow_two b
  unfold proposedIncrementCost
  omega

theorem second_increment_le_section (n m a b : Nat) :
    proposedIncrementCost ((nextMarker m)%3) (n+1)
      (nextExponent m a b) (nextRight b) ≤ (sectionResult (n+2) m a b).cost := by
  change _ ≤ proposedIncrementCost (m%3) (n+2) a b +
    (sectionResult (n+1) (nextMarker m) (nextExponent m a b) (nextRight b)).cost
  exact Nat.le_trans (sectionResult_firstCost_le n (nextMarker m)
    (nextExponent m a b) (nextRight b)) (Nat.le_add_left _ _)

theorem champion_ge_pow2600 : 2^2600 ≤ proposedTM63Moves + 7 := by
  have hb : 2600 ≤ nextRight 63 := by decide
  calc
    2^2600 ≤ 2^(nextRight 63) := Nat.pow_le_pow_right (by decide) hb
    _ ≤ proposedIncrementCost ((nextMarker 2)%3) 6
      (nextExponent 2 6 63) (nextRight 63) := increment_ge_pow _ _ _ _
    _ ≤ (sectionResult 7 2 6 63).cost := second_increment_le_section 5 2 6 63
    _ ≤ proposedTM63Moves + 7 := first_section_cost_le_champion_score

#print axioms champion_ge_pow2600
end BB6.Agent10LargeThreshold
