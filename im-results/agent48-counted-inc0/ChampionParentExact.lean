import ChampionParentCover
import ChampionLastHoleCover

namespace BB6.Agent48ChampionCylinder
open BB6Coverage BB6Coverage.Agent48Champion BB6ChampionArithmetic BB6.Agent13BlankDelay

theorem champion_score_ge_3512 : 3512 ≤ proposedTM63Moves+7 := by
  apply Eq.mp (congrArg (fun n : Nat => 3512 ≤ n) threeSectionScore_root)
  have h : 27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 := by
    simp only [threeSectionMoves]
    omega
  exact Nat.le_trans (by decide : 3512 ≤ 27959) h

theorem champion_parent_exact_cover :
    Cover (WeightedBound (proposedTM63Moves+7)) BB6.Agent48Parent.parent :=
  BB6.Agent48Parent.parent_cover _ champion_score_ge_3512 champion_last_hole_cover

noncomputable def championParentExactCertificate :
    WeightedTNFCertificate (proposedTM63Moves+7) BB6.Agent48Parent.parent 6 :=
  BB6.Agent48Parent.parentCertificate _ champion_score_ge_3512 champion_last_hole_cover

#print axioms champion_parent_exact_cover
#print axioms championParentExactCertificate
end BB6.Agent48ChampionCylinder
