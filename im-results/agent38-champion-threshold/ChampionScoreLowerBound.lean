import TM63RawUpperInterface
import Lean.Elab.Tactic.Omega

namespace BB6.Agent38ChampionThreshold

open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

theorem first_increment_ge_6766859 :
    6766859 ≤ proposedIncrementCost 2 7 6 63 := by
  have hpow : 6766859 ≤ 2^63 := by decide
  unfold proposedIncrementCost
  omega

theorem first_increment_le_first_section :
    proposedIncrementCost 2 7 6 63 ≤ (sectionResult 7 2 6 63).cost := by
  change proposedIncrementCost 2 7 6 63 ≤
    proposedIncrementCost (2 % 3) 7 6 63 +
      (sectionResult 6 (nextMarker 2) (nextExponent 2 6 63)
        (nextRight 63)).cost
  omega

theorem first_section_cost_le_champion_score :
    (sectionResult 7 2 6 63).cost ≤ proposedTM63Moves + 7 := by
  rw [← threeSectionMoves_root]
  simp only [threeSectionMoves]
  omega

theorem champion_score_ge_6766859 :
    6766859 ≤ proposedTM63Moves + 7 := by
  calc
    6766859 ≤ proposedIncrementCost 2 7 6 63 :=
      first_increment_ge_6766859
    _ ≤ (sectionResult 7 2 6 63).cost :=
      first_increment_le_first_section
    _ ≤ proposedTM63Moves + 7 :=
      first_section_cost_le_champion_score

#print axioms champion_score_ge_6766859

end BB6.Agent38ChampionThreshold
