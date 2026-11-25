import ChampionParentCover
import ChampionLastHoleCover
import TM63RawUpperInterface

namespace BB6.Agent48ChampionCylinder
open BB6Coverage BB6Coverage.Agent48Champion BB6ChampionArithmetic BB6.Agent13BlankDelay
open BB6Coverage.Agent48CountedInc0 BB6Coverage.Agent48DirectRoot

private theorem parent_rootSteps_le_score (rootSteps L n a b : Nat) :
    rootSteps ≤ threeSectionMoves rootSteps L n a b + 7 := by
  simp only [threeSectionMoves]
  omega

theorem champion_score_ge_3512 : 3512 ≤ proposedTM63Moves + 7 := by
  have hroot := parent_rootSteps_le_score 27959 3 7 6 63
  change 3512 ≤ proposedTM63Moves + 7
  rw [← threeSectionMoves_root]
  omega

theorem champion_parent_exact_cover :
    Cover (WeightedBound (proposedTM63Moves+7)) BB6.Agent48Parent.parent :=
  BB6.Agent48Parent.parent_cover _ champion_score_ge_3512 champion_last_hole_cover

noncomputable def championParentExactCertificate :
    WeightedTNFCertificate (proposedTM63Moves+7) BB6.Agent48Parent.parent 6 :=
  BB6.Agent48Parent.parentCertificate _ champion_score_ge_3512 champion_last_hole_cover

#print axioms champion_score_ge_3512
#print axioms champion_parent_exact_cover
#print axioms championParentExactCertificate
end BB6.Agent48ChampionCylinder
