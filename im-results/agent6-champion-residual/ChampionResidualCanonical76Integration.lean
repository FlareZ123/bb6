import ChampionF1ZeroRCIntegration
import Raw121Canonical77Graft

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6Canonical76ChampionIntegration

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
open BB6.Agent11Raw121
open BB6.Agent11Raw121Canonical77Graft

/-- Raw121 is a distinct C/0=0RD sibling, not the raw139 C/0=1LD parent. -/
theorem raw121_parent_not_raw139 :
    sameTable BB6.Agent11Raw121.p121 championResidual = false := by
  decide

/-- The raw139 champion-containing entry survives the accepted Raw121 graft
    into canonical77, yielding the 76-entry roster. -/
theorem championResidual_mem_canonical76 :
    (championResidualAddress, championResidual) ∈ roster76 := by
  decide

theorem championResidual_unique_canonical76 :
    (roster76.filter (fun e => e.1 == championResidualAddress)).length = 1 := by
  decide

theorem championResidual_unique_by_table :
    (roster76.filter (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

/-- The accepted Raw121 graft leaves 75 other canonical entries besides raw139. -/
theorem canonical76_other_address_count :
    (roster76.filter (fun e => e.1 != championResidualAddress)).length = 75 := by
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

/-- Prefix the canonical raw139 address to its 106 descendants, replacing
    exactly one of the 76 entries after the Raw121 graft. -/
noncomputable def refinedCanonical76Roster :
    List (List Move × PartialMachine) :=
  (roster76.filter (fun e => !sameTable e.2 championResidual)) ++
  (remainingF1ZeroRC.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem refinedCanonical76Roster_count :
    refinedCanonical76Roster.length = 181 := by
  decide

/-- Conditional exactness on the post-Raw121 76-roster: 75 other canonical
    Covers plus 106 raw139 descendant Covers suffice at the champion score. -/
theorem exact_from_canonical76_and_raw139_leaves
    (hOther : ∀ e ∈ roster76,
      e.2 ≠ championResidual →
        Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1ZeroRC,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent11Raw121Canonical77Graft.exact_at_target championScore
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

#print axioms raw121_parent_not_raw139
#print axioms championResidual_mem_canonical76
#print axioms championResidual_unique_canonical76
#print axioms championResidual_unique_by_table
#print axioms canonical76_other_address_count
#print axioms cover_championResidual_from_raw139_leaves
#print axioms refinedCanonical76Roster_count
#print axioms exact_from_canonical76_and_raw139_leaves

end BB6.Agent6Canonical76ChampionIntegration
