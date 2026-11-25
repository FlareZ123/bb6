import TM63RawUpperInterface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38ChampionThreshold

open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

/-- The first authentic source increment already costs at least 2^126
    primitive steps. The rest of the first section, both resets, the next
    two sections, and the terminal drain are all nonnegative additions. -/
theorem champion_score_ge_two_pow_126 :
    2^126 ≤ proposedTM63Moves + 7 := by
  have hfirst :
      proposedIncrementCost 2 7 6 63 ≤
        (sectionResult 7 2 6 63).cost := by
    change proposedIncrementCost 2 7 6 63 ≤
      proposedIncrementCost (2 % 3) 7 6 63 +
        (sectionResult 6 (nextMarker 2) (nextExponent 2 6 63)
          (nextRight 63)).cost
    exact Nat.le_add_right _ _
  have hcost :
      2^126 ≤ proposedIncrementCost 2 7 6 63 := by
    norm_num [proposedIncrementCost, v2]
  have hsection :
      2^126 ≤ (sectionResult 7 2 6 63).cost :=
    Nat.le_trans hcost hfirst
  rw [← threeSectionScore_root]
  unfold threeSectionMoves
  omega

/-- Conveniently lifts every parent certificate below 2^126 to the exact
    attained champion score, including the raw110 bound 6,766,859. -/
theorem champion_score_ge_6766859 :
    6766859 ≤ proposedTM63Moves + 7 :=
  Nat.le_trans (by norm_num : 6766859 ≤ 2^126)
    champion_score_ge_two_pow_126

#print axioms champion_score_ge_two_pow_126
#print axioms champion_score_ge_6766859

end BB6.Agent38ChampionThreshold
