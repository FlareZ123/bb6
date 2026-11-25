import ChampionF1ZeroRCIntegration
import CanonicalRaw114Accepted

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6Canonical77ChampionIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent48F1Integration
open BB6.Agent48F1RFIntegration
open BB6.Agent48F1ZeroLFIntegration
open BB6.Agent6F1OneLAIntegration
open BB6.Agent6F1ZeroRCIntegration
open BB6.Agent47CanonicalRefinement

/-- The raw139 champion-containing entry survives the accepted raw114 graft:
    its exact address and partial table remain in the canonical77 roster. -/
theorem championResidual_mem_canonical77 :
    (championResidualAddress, championResidual) ∈
      BB6.Agent47CanonicalRaw114Accepted.roster := by
  decide

/-- The raw139 address occurs exactly once after the raw114 graft. -/
theorem championResidual_unique_canonical77 :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter
      (fun e => e.1 = championResidualAddress)).length = 1 := by
  decide

/-- There is exactly one entry whose table is the raw139 parent, not merely
    one entry with its address. -/
theorem championResidual_unique_by_table :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter
      (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

/-- The accepted 77-entry canonical roster therefore has 76 other entries. -/
theorem canonical77_other_address_count :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter
      (fun e => e.1 ≠ championResidualAddress)).length = 76 := by
  decide

/-- Covers for the 106 retained raw139 descendants lift through all accepted
    sibling grafts and the F0 refinement to a cover of the original raw139
    champion-containing cylinder. -/
theorem cover_championResidual_from_raw139_leaves
    (hLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual := by
  have h107 : ∀ e ∈ remainingF1OneLA,
      Cover (WeightedBound championScore) e.2 :=
    fun e he => cover_remainingF1OneLA hLeaves e he
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

/-- Prefixing the raw139 address to its 106 descendants replaces precisely
    one canonical77 entry by a disjoint, explicit residual family. -/
noncomputable def refinedCanonical77Roster :
    List (List Move × PartialMachine) :=
  (BB6.Agent47CanonicalRaw114Accepted.roster.filter
    (fun e => sameTable e.2 championResidual = false)) ++
  (remainingF1ZeroRC.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem refinedCanonical77Roster_count :
    refinedCanonical77Roster.length = 182 := by
  decide

/-- The current best accepted root interface is canonical77, not the older
    canonical78 interface. Its 76 non-raw139 Covers plus 106 raw139 descendant
    Covers suffice for exact BB(6) at the attained champion score. -/
theorem exact_from_canonical77_and_raw139_leaves
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent47CanonicalRaw114Accepted.exact_at_target championScore
    (Nat.le_trans (by decide) champion_score_ge_49394)
    (by
      intro e he
      by_cases hSame : sameTable e.2 championResidual = true
      · have heq : e.2 = championResidual := sameTable_sound hSame
        rw [heq]
        exact cover_championResidual_from_raw139_leaves hLeaves
      · have hne : e.2 ≠ championResidual := by
          intro hEq
          have hself : sameTable championResidual championResidual = true := by decide
          exact hSame (by simpa [hEq] using hself)
        exact hOther e he hne)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_canonical77
#print axioms championResidual_unique_canonical77
#print axioms championResidual_unique_by_table
#print axioms canonical77_other_address_count
#print axioms cover_championResidual_from_raw139_leaves
#print axioms refinedCanonical77Roster_count
#print axioms exact_from_canonical77_and_raw139_leaves

end BB6.Agent6Canonical77ChampionIntegration
