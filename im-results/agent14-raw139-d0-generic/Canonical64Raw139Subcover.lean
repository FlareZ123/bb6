import Canonical64Raw120Integrated
import ChampionResidualCanonical68Integration
import A6Ingestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical64Raw139Subcover

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent3Canonical64Raw120
open BB6.Agent6ChampionResidual
open BB6.Agent6ChampionRaw139SiblingExtended

/-- The champion-containing Raw139 parent survives the three extra parent
    cuts and the Raw120 cut in the accepted Canonical64 roster. -/
theorem championResidual_mem_roster64 :
    ∃ e ∈ roster64, sameTable e.2 championResidual = true := by decide

/-- It occurs exactly once in the 64-entry quotient roster. -/
theorem championResidual_unique_in_roster64 :
    (roster64.filter (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

/-- The pinned Cryptids A6 leaf, after forgetting explicit halt rows,
    is a one-hole partial machine in the current 80-leaf Raw139 complement. -/
abbrev a6Leaf : PartialMachine :=
  BB6.Agent47WeightedHalt.forgetHaltRows BB6.Agent19HardRoot.A6

theorem a6Leaf_mem_remainingRaw139AfterFortyThree :
    ∃ e ∈ remainingRaw139AfterFortyThree, sameTable e.2 a6Leaf = true := by
  decide

theorem a6Leaf_unique_in_remainingRaw139AfterFortyThree :
    (remainingRaw139AfterFortyThree.filter
      (fun e => sameTable e.2 a6Leaf)).length = 1 := by
  decide

def remainingRaw139AfterA6 : List (List Move × PartialMachine) :=
  remainingRaw139AfterFortyThree.filter (fun e => !sameTable e.2 a6Leaf)

theorem raw139_remaining_after_A6_count :
    remainingRaw139AfterA6.length = 79 := by
  decide

/-- The A6 literal nonhalting theorem supplies a source-accepted weighted
    Cover for its unique matching residual leaf, leaving 79 Raw139 Covers. -/
theorem cover_championResidual_after_A6
    (hRaw139 : ∀ e ∈ remainingRaw139AfterA6,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    Cover (WeightedBound (proposedTM63Moves + 7)) championResidual :=
  cover_championResidual_after_fortyThree (fun e he => by
    by_cases hs : sameTable e.2 a6Leaf = true
    · have hEq : e.2 = a6Leaf := sameTable_sound hs
      rw [hEq]
      exact BB6.Agent48A6Ingestion.A6_weighted_cover
        (proposedTM63Moves + 7)
    · have hFalse : sameTable e.2 a6Leaf = false := by
        cases h : sameTable e.2 a6Leaf <;> simp_all
      have hmem : e ∈ remainingRaw139AfterA6 := by
        simp [remainingRaw139AfterA6, List.mem_filter, he, hFalse]
      exact hRaw139 e hmem)

/-- The current conditional interface has 63 other Canonical64 Covers and
    79 Raw139 descendant Covers, after discharging A6 with its pinned source
    nonhalting theorem. This is still a local decomposition, not a new roster. -/
theorem raw139_refined_obligation_count :
    (roster64.filter (fun e => !sameTable e.2 championResidual)).length +
      remainingRaw139AfterA6.length = 142 := by
  decide

/-- The existing Canonical64 exactness theorem with its championResidual
    Cover hypothesis discharged by the 43 sibling Covers, the A6 source
    Cover, and 79 remaining Raw139 descendant Covers. -/
theorem exact_at_target_with_raw139_subcover
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hRaw139 : ∀ e ∈ remainingRaw139AfterA6,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent3Canonical64Raw120.exact_at_target
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (fun e he => by
      by_cases hs : sameTable e.2 championResidual = true
      · have hEq : e.2 = championResidual := sameTable_sound hs
        rw [hEq]
        exact cover_championResidual_after_A6 hRaw139
      · have hne : e.2 ≠ championResidual := by
          intro hEq
          have hself : sameTable championResidual championResidual = true := by decide
          exact hs (by simpa [hEq] using hself)
        exact hOther e he hne)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_roster64
#print axioms championResidual_unique_in_roster64
#print axioms a6Leaf_mem_remainingRaw139AfterFortyThree
#print axioms a6Leaf_unique_in_remainingRaw139AfterFortyThree
#print axioms raw139_remaining_after_A6_count
#print axioms raw139_refined_obligation_count
#print axioms exact_at_target_with_raw139_subcover

end BB6.Agent14Canonical64Raw139Subcover
