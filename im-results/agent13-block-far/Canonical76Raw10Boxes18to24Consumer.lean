import CanonicalTwoParentRosterOnly
import Canonical76Raw10Membership
import Canonical77ExactComposition
import Raw10Box18to24CombinedBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13Canonical76Raw10Boxes18to24Consumer

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalTwoParent

abbrev Parent := BB6.Agent49Box18to24CombinedBridge.Parent
abbrev Remainder := BB6.Agent49Box18to24CombinedBridge.CombinedRemainder

/-- The source bridge and the canonical76 membership module name the same
    exact B0=1LC partial table. -/
theorem raw10Parent_eq_parent :
    BB6.Agent50Canonical76Raw10.raw10Parent = Parent := by
  decide

/-- Canonical76 exactness with the seven source-accepted rectangles removed
    from the raw10 local obligations. The 34-box false-match complement and
    the other 75 canonical representatives remain explicit at score B. -/
theorem exact_at_champion_score
    (hOpen :
      ∀ r ∈ Remainder,
        BB6.Agent49Box18to24CombinedBridge.closedMatchCombined r = false →
          ∀ m : BB6Coverage.Machine,
            BB6.Agent49Box.Fits r m →
              WeightedBound BB6.Agent31Canonical77Exact.championScore m)
    (hOther :
      ∀ e ∈ BB6.Agent50Canonical76Raw10.otherRoster,
        Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent31Canonical77Exact.championScore := by
  let B := BB6.Agent31Canonical77Exact.championScore
  have hB : 7014 ≤ B :=
    Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014
  have hLeaves :
      ∀ e ∈ roster76, Cover (WeightedBound B) e.2 := by
    intro e he
    by_cases hs : sameTable e.2 BB6.Agent50Canonical76Raw10.raw10Parent = true
    · have heq : e.2 = BB6.Agent50Canonical76Raw10.raw10Parent :=
        sameTable_sound hs
      rw [heq, raw10Parent_eq_parent]
      exact BB6.Agent49Box18to24CombinedBridge.raw10_cover_with_cycle_halt_boxes18to24
        B hB hOpen
    · have hmem : e ∈ BB6.Agent50Canonical76Raw10.otherRoster := by
        apply List.mem_filter.mpr
        exact ⟨he, by simp [hs]⟩
      exact hOther e hmem
  exact BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target B hB hLeaves
    BB6.Agent48DirectRoot.champion_raw_witness

#print axioms raw10Parent_eq_parent
#print axioms exact_at_champion_score

end BB6.Agent13Canonical76Raw10Boxes18to24Consumer
