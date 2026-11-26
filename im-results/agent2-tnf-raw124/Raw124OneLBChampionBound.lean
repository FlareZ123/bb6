import TM63RawUpperInterface
import TM63DirectRootComposition

namespace BB6.Agent2Raw124OneLBChampionBound

open BB6ChampionArithmetic

/-- The authenticated blank-root prefix alone already exceeds the 1LB
    branch cutoff.  This avoids depending on the still-unaccepted F412
    two-million-step adapter. -/
theorem champion_ge_27959 : 27959 ≤ proposedTM63Moves + 7 := by
  have hroot :
      27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 :=
    BB6Coverage.Agent48DirectRoot.rootSteps_le_score 27959 3 7 6 63
  exact Eq.mp
    (congrArg (fun n : Nat => 27959 ≤ n + 7)
      BB6Coverage.Agent48DirectRoot.threeSectionMoves_root)
    hroot

/-- Any Raw124 F1=1LB weighted certificate at the established cutoff 3006
    lifts directly to the exact attained champion score. -/
theorem branch_bound_le_champion_1lb (B : Nat) (hB : B ≤ 3006) :
    B ≤ proposedTM63Moves + 7 :=
  Nat.le_trans hB
    (Nat.le_trans (by decide : 3006 ≤ 27959) champion_ge_27959)

#print axioms champion_ge_27959
#print axioms branch_bound_le_champion_1lb

end BB6.Agent2Raw124OneLBChampionBound
