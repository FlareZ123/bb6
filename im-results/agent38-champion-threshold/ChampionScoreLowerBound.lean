import TM63RawUpperInterface
import CostRecurrence
import Lean.Elab.Tactic.Omega

namespace BB6.Agent38ChampionThreshold

open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

/-- The first proposed source increment already exceeds 2^63. -/
theorem first_increment_ge_pow63 :
    2^63 ≤ proposedIncrementCost 2 7 6 63 := by
  have hsmall : 14 ≤ 2^63 := by decide
  unfold proposedIncrementCost
  omega

/-- Generic first-cost inequality. The symbolic successor parameter
    keeps the residual section opaque, so no tower-sized right endpoint is
    evaluated by the kernel. -/
theorem sectionResult_firstCost_le (n m a b : Nat) :
    proposedIncrementCost (m%3) (n+1) a b ≤
      (sectionResult (n+1) m a b).cost := by
  simp only [sectionResult]
  exact Nat.le_add_right _ _

/-- The initial proposed increment is one summand of the initial section. -/
theorem first_increment_le_first_section :
    proposedIncrementCost 2 7 6 63 ≤ (sectionResult 7 2 6 63).cost :=
  sectionResult_firstCost_le 6 2 6 63

/-- For symbolic section parameters, the first section cost is one
    nonnegative summand of the full three-section composition. Keeping the
    parameters symbolic avoids reducing the later tower-sized sections. -/
theorem sectionResult_cost_le_threeSectionMoves
    (rootSteps L n a b : Nat) :
    (sectionResult n 2 a b).cost ≤ threeSectionMoves rootSteps L n a b := by
  -- Expose the local lets so omega sees the same sectionResult cost on both
  -- sides, without unfolding the recursive state itself.
  dsimp [threeSectionMoves]
  omega

/-- The three-section score contains the complete first section cost. -/
theorem first_section_cost_le_champion_score :
    (sectionResult 7 2 6 63).cost ≤ proposedTM63Moves + 7 := by
  have h :
      (sectionResult 7 2 6 63).cost ≤
        threeSectionMoves 27959 3 7 6 63 + 7 :=
    Nat.le_trans
      (sectionResult_cost_le_threeSectionMoves 27959 3 7 6 63)
      (Nat.le_add_right _ _)
  exact Eq.mp
    (congrArg (fun n : Nat =>
      (sectionResult 7 2 6 63).cost ≤ n + 7) threeSectionMoves_root)
    h

/-- The exact champion score exceeds 2^63. This stronger bound can lift any
    smaller finite-parent threshold without unfolding the enormous score. -/
theorem champion_score_ge_pow63 :
    2^63 ≤ proposedTM63Moves + 7 := by
  calc
    2^63 ≤ proposedIncrementCost 2 7 6 63 :=
      first_increment_ge_pow63
    _ ≤ (sectionResult 7 2 6 63).cost :=
      first_increment_le_first_section
    _ ≤ proposedTM63Moves + 7 :=
      first_section_cost_le_champion_score

/-- In particular, the champion score exceeds the Raw110 late-parent
    threshold required by the Raw121 + Raw110 roster. -/
theorem champion_score_ge_6766859 :
    6766859 ≤ proposedTM63Moves + 7 := by
  exact Nat.le_trans (by decide : 6766859 ≤ 2^63) champion_score_ge_pow63

#print axioms sectionResult_firstCost_le
#print axioms first_increment_ge_pow63
#print axioms first_increment_le_first_section
#print axioms sectionResult_cost_le_threeSectionMoves
#print axioms first_section_cost_le_champion_score
#print axioms champion_score_ge_pow63
#print axioms champion_score_ge_6766859

end BB6.Agent38ChampionThreshold
