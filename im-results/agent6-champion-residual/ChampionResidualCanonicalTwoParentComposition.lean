import ChampionF1OneLBIntegration
import CanonicalTwoParentRosterOnly

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6CanonicalTwoParentComposition

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent13MixedBound109
open BB6.Agent31Canonical78Exact
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent48F1Integration
open BB6.Agent48F1RFIntegration
open BB6.Agent48F1ZeroLFIntegration
open BB6.Agent6F1OneLAIntegration
open BB6.Agent6F1ZeroRCIntegration
open BB6.Agent41F1ZeroRBZeroLAOneRDIntegration
open BB6.Agent6F1OneLBIntegration
open BB6.Agent47CanonicalTwoParent
open BB6.Agent31CanonicalTwoParentRosterOnly

/-- Raw139 is exactly one entry of the accepted 76-residual two-parent
    quotient roster. Membership is checked by its address and pointwise
    table equality, not by matching labels. -/
theorem championResidual_mem_roster76 :
    ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      e.1 = championResidualAddress ∧
      sameTable e.2 championResidual = true := by
  decide

/-- The champion parent occurs once in the 76-entry roster by address. -/
theorem championResidual_unique_roster76 :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => e.1 == championResidualAddress)).length = 1 := by
  decide

/-- The champion parent occurs once in the 76-entry roster by exact table. -/
theorem championResidual_unique_by_table :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

/-- The accepted 76-roster leaves 75 other canonical parent obligations. -/
theorem canonical76_other_address_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => e.1 != championResidualAddress)).length = 75 := by
  decide

theorem canonical76_other_table_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 championResidual))).length = 75 := by
  decide

/-- Compose the source-accepted F1 sibling Covers: 102 retained descendants
    lift through 1LB, 0RB/0LA/1RD, 0RC, 1LA, 0LF, 0RF and the F0 refinement
    to a Cover of the original champion-containing raw139 cylinder. -/
theorem cover_championResidual_from_102_leaves
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLB,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual := by
  have h103 : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRD,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1AfterZeroRBZeroLAOneRD hLeaves e he
  have h106 : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1ZeroRC h103 e he
  have h107 : ∀ e ∈ remainingF1OneLA,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1OneLA h106 e he
  have h108 : ∀ e ∈ remainingF1ZeroLF,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1ZeroLF h107 e he
  have h109 : ∀ e ∈ remainingF1RF,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1RF h108 e he
  have h110 : ∀ e ∈ remainingF1Extended,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1Extended h109 e he
  have h112 : ∀ e ∈ remainingExtended,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingExtended h110 e he
  exact BB6.Agent41F0Extended.refined_residual_cover h112

/-- Replace the unique raw139 parent in the accepted 76-roster by the 102
    retained F1-refined residual cylinders. -/
noncomputable def refinedCanonical76Roster : List (List Move × PartialMachine) :=
  (BB6.Agent47CanonicalTwoParent.roster76.filter
    (fun e => !(sameTable e.2 championResidual))) ++
  (remainingF1AfterZeroRBZeroLAOneRDOneLB.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem total_remaining_obligations_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 championResidual))).length +
      remainingF1AfterZeroRBZeroLAOneRDOneLB.length = 177 := by
  rw [canonical76_other_table_count,
    BB6.Agent6F1OneLBIntegration.remainingF1AfterZeroRBZeroLAOneRDOneLB_count]
  rfl

theorem refinedCanonical76Roster_count :
    refinedCanonical76Roster.length = 177 := by
  decide

/-- The 177 obligation addresses are pairwise distinct. -/
theorem refinedCanonical76Roster_addresses_nodup :
    (refinedCanonical76Roster.map Prod.fst).Nodup := by
  decide

/-- Conditional exactness at the attained champion score: 75 untouched
    canonical Covers plus 102 raw139 descendant Covers suffice. -/
theorem exact_from_canonical76_and_102_raw139_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      sameTable e.2 championResidual = false →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLB,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore := by
  apply BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target
    championScore (Nat.le_of_lt BB6.Agent31Canonical78Exact.champion_score_gt_7014)
  · intro e he
    by_cases hs : sameTable e.2 championResidual = true
    · have heq : e.2 = championResidual := sameTable_sound hs
      simpa [heq] using cover_championResidual_from_102_leaves hLeaves
    · have hfalse : sameTable e.2 championResidual = false := by
        cases h : sameTable e.2 championResidual <;> simp_all
      exact hOther e he hfalse
  · exact BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_roster76
#print axioms championResidual_unique_roster76
#print axioms championResidual_unique_by_table
#print axioms canonical76_other_address_count
#print axioms canonical76_other_table_count
#print axioms cover_championResidual_from_102_leaves
#print axioms total_remaining_obligations_count
#print axioms refinedCanonical76Roster_count
#print axioms refinedCanonical76Roster_addresses_nodup
#print axioms exact_from_canonical76_and_102_raw139_leaves

end BB6.Agent6CanonicalTwoParentComposition
