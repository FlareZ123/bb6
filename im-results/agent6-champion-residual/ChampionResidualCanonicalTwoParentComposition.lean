import F0SiblingIntegrationExtended
import CanonicalTwoParentRosterOnly

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6CanonicalTwoParentComposition

/-- Raw139 is exactly one entry of the accepted 76-residual two-parent
    quotient roster. This is an exact table/address membership statement. -/
theorem championResidual_mem_roster76 :
    (BB6.Agent31ChampionParentIntegration.championResidualAddress,
      BB6.Agent6ChampionResidual.championResidual) ∈
        BB6.Agent47CanonicalTwoParent.roster76 := by
  decide

/-- The champion parent occurs once in the 76-entry roster. -/
theorem championResidual_unique_roster76 :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => e.2 = BB6.Agent6ChampionResidual.championResidual)).length = 1 := by
  decide

/-- The 75 nonchampion parents remain as the untouched part of the accepted
    two-parent roster. -/
theorem nonchampion_roster_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => e.2 ≠ BB6.Agent6ChampionResidual.championResidual)).length = 75 := by
  decide

/-- Replace the single raw139 parent by the 112 residual cylinders already
    discharged to the F0 sibling refinement interface: 75 + 112 = 187
    proof obligations remain. -/
theorem total_remaining_obligations_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => e.2 ≠ BB6.Agent6ChampionResidual.championResidual)).length +
      BB6.Agent41F0Extended.remainingExtended.length = 187 := by
  rw [nonchampion_roster_count,
    BB6.Agent41F0Extended.remainingExtended_count]
  rfl

/-- Conditional exactness at the attained champion score from Covers for the
    75 untouched canonical parents and the 112 raw139 frontier residuals. -/
theorem exact_from_other_roster_covers_and_remaining_extended
    (hOther : ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      e.2 ≠ BB6.Agent6ChampionResidual.championResidual →
        Cover (WeightedBound BB6.Agent13MixedBound109.championScore) e.2)
    (hLeaves : ∀ e ∈ BB6.Agent41F0Extended.remainingExtended,
      Cover (WeightedBound BB6.Agent13MixedBound109.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent13MixedBound109.championScore := by
  apply BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target
    BB6.Agent13MixedBound109.championScore
    (Nat.le_of_lt BB6.Agent31Canonical78Exact.champion_score_gt_7014)
  · intro e he
    by_cases hEq : e.2 = BB6.Agent6ChampionResidual.championResidual
    · simpa [hEq] using
        BB6.Agent41F0Extended.refined_residual_cover hLeaves
    · exact hOther e he hEq
  · exact BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_roster76
#print axioms championResidual_unique_roster76
#print axioms nonchampion_roster_count
#print axioms total_remaining_obligations_count
#print axioms exact_from_other_roster_covers_and_remaining_extended

end BB6.Agent6CanonicalTwoParentComposition
