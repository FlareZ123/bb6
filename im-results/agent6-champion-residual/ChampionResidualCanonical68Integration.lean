import ChampionResidualSourceSiblingIntegrationExtended
import Canonical68E1ParentGraft
import ChampionScoreLowerBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent6Canonical68ChampionIntegration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent6ChampionRaw139SiblingExtended
open BB6.Agent6Canonical68E1ParentGraft
open BB6.Agent31Canonical74Raw109Raw123

/-- The champion-containing raw139 parent survives all eight accepted E1
    parent cuts and remains a named entry of the accepted Canonical68 roster. -/
theorem championResidual_mem_canonical68 :
    (championResidualAddress, championResidual) ∈ roster68 := by
  decide

theorem championResidual_unique_canonical68 :
    (roster68.filter (fun e => e.1 == championResidualAddress)).length = 1 := by
  decide

theorem championResidual_unique_by_table_canonical68 :
    (roster68.filter (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

theorem canonical68_other_address_count :
    (roster68.filter (fun e => e.1 != championResidualAddress)).length = 67 := by
  decide

theorem canonical68_other_table_count :
    (roster68.filter (fun e => !sameTable e.2 championResidual)).length = 67 := by
  decide

/-- Replace the one retained raw139 parent by its exact twenty-six-sibling
    refinement. The 67 other Canonical68 representatives are unchanged. -/
noncomputable def refinedCanonical68Roster :
    List (List Move × PartialMachine) :=
  (roster68.filter (fun e => !sameTable e.2 championResidual)) ++
  (remainingRaw139AfterThirtyEight.map
    (fun e => (championResidualAddress ++ e.1, e.2)))

theorem refinedCanonical68Roster_count :
    refinedCanonical68Roster.length = 152 := by
  simp [refinedCanonical68Roster, canonical68_other_table_count,
    remainingRaw139AfterThirtyEight_count]

/-- Source-authentic conditional exactness at the attained champion score.
    The eight E1 parent Covers, 67 other Canonical68 Covers, and 85 retained
    raw139 descendant Covers are the only remaining Cover premises. -/
theorem exact_from_canonical68_and_raw139_after_thirtyEight
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (h60 : Cover (WeightedBound 1175) p60)
    (h110 : Cover (WeightedBound 6766859) p110)
    (h111 : Cover (WeightedBound 7014) p111)
    (h117 : Cover (WeightedBound 1291) p117)
    (h121 : Cover (WeightedBound 4063) p121)
    (h125 : Cover (WeightedBound 1290) p125)
    (hOther : ∀ e ∈ roster68,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hLeaves : ∀ e ∈ remainingRaw139AfterThirtyEight,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent6Canonical68E1ParentGraft.exact_at_target
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    h109 h123 h60 h110 h111 h117 h121 h125
    (fun e he => by
      by_cases hSame : sameTable e.2 championResidual = true
      · have heq : e.2 = championResidual := sameTable_sound hSame
        rw [heq]
        exact cover_championResidual_after_thirtyEight hLeaves
      · have hne : e.2 ≠ championResidual := by
          intro hEq
          have hself : sameTable championResidual championResidual = true := by decide
          exact hSame (by simpa [hEq] using hself)
        exact hOther e he hne)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_canonical68
#print axioms championResidual_unique_canonical68
#print axioms championResidual_unique_by_table_canonical68
#print axioms canonical68_other_address_count
#print axioms canonical68_other_table_count
#print axioms refinedCanonical68Roster_count
#print axioms exact_from_canonical68_and_raw139_after_thirtyEight

end BB6.Agent6Canonical68ChampionIntegration
