import Canonical64Raw120Integrated
import ChampionResidualCanonical68Integration
import Raw139Normalized
import Raw139E0ZeroRAIntegrated

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical64Raw139Subcover

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent3Canonical64Raw120
open BB6.Agent6ChampionResidual
open BB6.Agent6ChampionRaw139SiblingExtended
open BB6.Agent6Raw139Normalized
open BB6.Agent3Raw139E0ZeroRAIntegrated

/-- The champion-containing Raw139 parent survives the three extra parent
    cuts and the Raw120 cut in the accepted Canonical64 roster. -/
theorem championResidual_mem_roster64 :
    ∃ e ∈ roster64, sameTable e.2 championResidual = true := by decide

/-- It occurs exactly once in the 64-entry quotient roster. -/
theorem championResidual_unique_in_roster64 :
    (roster64.filter (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

/-- The E0=0RA six-hole table is tested against the *active* 80-leaf
    Canonical68 descendant list, not merely the historical Canonical77 list. -/
def e0Table : PartialMachine := leaf dischargedRow

theorem e0_table_present_in_raw139_after_fortyThree :
    ∃ e ∈ remainingRaw139AfterFortyThree,
      sameTable e.2 e0Table = true := by decide

theorem e0_table_occurs_once_in_raw139_after_fortyThree :
    (remainingRaw139AfterFortyThree.filter
      (fun e => sameTable e.2 e0Table)).length = 1 := by decide

/-- The source-accepted E0=0RA Cover at 321,796 lifts to the exact champion
    score by monotonicity of the weighted bound. -/
theorem e0_cover_at_champion_score :
    Cover (WeightedBound (proposedTM63Moves + 7)) e0Table := by
  cases BB6.Agent3Raw139E0ZeroRAIntegrated.discharged_cover with
  | leaf p hbound =>
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans (hbound m hm k d hk hd) (by omega)

/-- The 80-leaf list with its unique E0=0RA table removed. -/
def remainingRaw139AfterFortyThreeWithoutE0 :=
  remainingRaw139AfterFortyThree.filter (fun e => !sameTable e.2 e0Table)

theorem remainingRaw139AfterFortyThreeWithoutE0_count :
    remainingRaw139AfterFortyThreeWithoutE0.length = 79 := by decide

theorem cover_remainingRaw139_after_e0
    (h : ∀ e ∈ remainingRaw139AfterFortyThreeWithoutE0,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    ∀ e ∈ remainingRaw139AfterFortyThree,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2 := by
  intro e he
  by_cases hs : sameTable e.2 e0Table = true
  · have hEq : e.2 = e0Table := sameTable_sound hs
    rw [hEq]
    exact e0_cover_at_champion_score
  · exact h e (List.mem_filter.mpr ⟨he, by simp [hs]⟩)

/-- After replacing the champion parent by the 43 source-accepted sibling
    Covers and 79 remaining Raw139 descendant Covers, the conditional
    interface has 63 other Canonical64 Covers and 79 Raw139 Covers. -/
theorem raw139_refined_obligation_count :
    (roster64.filter (fun e => !sameTable e.2 championResidual)).length +
      remainingRaw139AfterFortyThreeWithoutE0.length = 142 := by
  decide

/-- The existing Canonical64 exactness theorem with its championResidual
    Cover hypothesis discharged by the 43 source-accepted Raw139 sibling
    Covers, the E0=0RA Cover, and the 79 remaining descendant Covers. -/
theorem exact_at_target_with_raw139_subcover
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hRaw139 : ∀ e ∈ remainingRaw139AfterFortyThreeWithoutE0,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent3Canonical64Raw120.exact_at_target
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (fun e he => by
      by_cases hs : sameTable e.2 championResidual = true
      · have hEq : e.2 = championResidual := sameTable_sound hs
        rw [hEq]
        exact cover_championResidual_after_fortyThree
          (cover_remainingRaw139_after_e0 hRaw139)
      · have hne : e.2 ≠ championResidual := by
          intro hEq
          have hself : sameTable championResidual championResidual = true := by decide
          exact hs (by simpa [hEq] using hself)
        exact hOther e he hne)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms championResidual_mem_roster64
#print axioms championResidual_unique_in_roster64
#print axioms raw139_refined_obligation_count
#print axioms exact_at_target_with_raw139_subcover

end BB6.Agent14Canonical64Raw139Subcover
