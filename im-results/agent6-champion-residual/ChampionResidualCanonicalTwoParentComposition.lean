import F0SiblingIntegrationExtended
import CanonicalTwoParentRosterOnly

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6CanonicalTwoParentComposition

open BB6Coverage

/-- Raw139 is exactly one entry of the accepted 76-residual two-parent
    quotient roster. Membership is checked by its address and pointwise
    table equality, not by matching labels. -/
theorem championResidual_mem_roster76 :
    ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      e.1 = BB6.Agent31ChampionParentIntegration.championResidualAddress ∧
      sameTable e.2 BB6.Agent6ChampionResidual.championResidual = true := by
  decide

/-- The champion parent occurs once in the 76-entry roster. -/
theorem championResidual_unique_roster76 :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => sameTable e.2 BB6.Agent6ChampionResidual.championResidual)).length = 1 := by
  decide

/-- The 75 nonchampion parents remain as the untouched part of the accepted
    two-parent roster. -/
theorem nonchampion_roster_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 BB6.Agent6ChampionResidual.championResidual))).length = 75 := by
  decide

/-- Replace the single raw139 parent by the 112 residual cylinders already
    discharged to the F0 sibling refinement interface: 75 + 112 = 187
    proof obligations remain. -/
theorem total_remaining_obligations_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 BB6.Agent6ChampionResidual.championResidual))).length +
      BB6.Agent41F0Extended.remainingExtended.length = 187 := by
  rw [nonchampion_roster_count,
    BB6.Agent41F0Extended.remainingExtended_count]
  rfl

/-- Conditional exactness at the attained champion score from Covers for the
    75 untouched canonical parents and the 112 raw139 frontier residuals. -/
theorem exact_from_other_roster_covers_and_remaining_extended
    (hOther : ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      sameTable e.2 BB6.Agent6ChampionResidual.championResidual = false →
        Cover (WeightedBound BB6.Agent13MixedBound109.championScore) e.2)
    (hLeaves : ∀ e ∈ BB6.Agent41F0Extended.remainingExtended,
      Cover (WeightedBound BB6.Agent13MixedBound109.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent13MixedBound109.championScore := by
  apply BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target
    BB6.Agent13MixedBound109.championScore
    (Nat.le_of_lt BB6.Agent31Canonical78Exact.champion_score_gt_7014)
  · intro e he
    by_cases hs : sameTable e.2 BB6.Agent6ChampionResidual.championResidual = true
    · have heq : e.2 = BB6.Agent6ChampionResidual.championResidual :=
        sameTable_sound hs
      simpa [heq] using
        BB6.Agent41F0Extended.refined_residual_cover hLeaves
    · have hfalse :
          sameTable e.2 BB6.Agent6ChampionResidual.championResidual = false := by
        cases h : sameTable e.2 BB6.Agent6ChampionResidual.championResidual <;> simp_all
      exact hOther e he hfalse
  · exact BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_roster76
#print axioms championResidual_unique_roster76
#print axioms nonchampion_roster_count
#print axioms total_remaining_obligations_count
#print axioms exact_from_other_roster_covers_and_remaining_extended

end BB6.Agent6CanonicalTwoParentComposition
