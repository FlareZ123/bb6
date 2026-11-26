import Canonical64Raw120Integrated
import ChampionResidualCanonical68Integration

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

/-- After replacing that one parent obligation by the 43-sibling Raw139
    decomposition, the conditional interface has 63 other quotient Covers
    and 80 Raw139 descendant Covers. This is a local decomposition of the
    existing Canonical64 proof, not a new global roster. -/
theorem raw139_refined_obligation_count :
    (roster64.filter (fun e => !sameTable e.2 championResidual)).length +
      remainingRaw139AfterFortyThree.length = 143 := by
  decide

/-- The existing Canonical64 exactness theorem with its championResidual
    Cover hypothesis discharged compositionally by the 43 source-accepted
    Raw139 sibling Covers and the 80 remaining Raw139 descendant Covers. -/
theorem exact_at_target_with_raw139_subcover
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hRaw139 : ∀ e ∈ remainingRaw139AfterFortyThree,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent3Canonical64Raw120.exact_at_target
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (fun e he => by
      by_cases hs : sameTable e.2 championResidual = true
      · have hEq : e.2 = championResidual := sameTable_sound hs
        rw [hEq]
        exact cover_championResidual_after_fortyThree hRaw139
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
