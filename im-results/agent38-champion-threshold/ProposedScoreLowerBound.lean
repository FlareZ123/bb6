import TM63RawUpperInterface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38ProposedScoreThreshold

open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

/-- The first section cost is one summand of the proposed complete
    three-section score; all other terms in the expression are nonnegative. -/
private theorem first_section_cost_le_three_section_score
    (rootSteps L n a b : Nat) :
    (sectionResult n 2 a b).cost ≤
      threeSectionMoves rootSteps L n a b + 7 := by
  unfold threeSectionMoves
  omega

/-- Arithmetic bound on the proposed score expression. This is not yet an
    actual runtime lower bound: the original-machine IncrementSource and
    ResetSource closures used to attain this score remain pending audit. -/
theorem proposed_score_ge_two_pow_126 :
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
  have hscore := first_section_cost_le_three_section_score 27959 3 7 6 63
  rw [← threeSectionScore_root]
  exact Nat.le_trans hsection hscore

/-- Arithmetic corollary for the raw110 parent threshold. It becomes a
    champion-runtime bound only after the proposed score is source-attained. -/
theorem proposed_score_ge_6766859 :
    6766859 ≤ proposedTM63Moves + 7 :=
  Nat.le_trans (by norm_num : 6766859 ≤ 2^126)
    proposed_score_ge_two_pow_126

#print axioms proposed_score_ge_two_pow_126
#print axioms proposed_score_ge_6766859

end BB6.Agent38ProposedScoreThreshold
