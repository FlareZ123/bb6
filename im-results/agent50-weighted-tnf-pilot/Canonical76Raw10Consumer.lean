import CanonicalTwoParentAccepted
import Canonical76Raw10Membership
import HeldBlockRaw10Combined

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Canonical76Raw10

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalTwoParent

/-- Three-parent conditional exactness consumer.

The two-parent quotient dichotomy is unchanged. One of its 76 obligations is
resolved by the B0=1LC cover assembled from the 65 side witnesses, the
held BlockFAR leaf, Agent50's 625-machine lasso cylinder, and the
25^8 forced-halt cylinder. The only remaining local obligations are the
41 exact complement boxes; the other 75 canonical representatives still
need their own Covers at the attained champion score.

This is a conditional reduction, not a completed BB(6) upper bound. -/
theorem exact_from_raw10_remainder_at_champion_score
    (hOpen :
      ∀ r ∈ BB6.Agent17Raw10CombinedConsumer.raw10RemainderWithCycleAndHalt,
        ∀ m, BB6.Agent49Box.Fits r m →
          WeightedBound BB6.Agent31Canonical77Exact.championScore m)
    (hOther :
      ∀ e ∈ otherRoster,
        Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent31Canonical77Exact.championScore := by
  let B := BB6.Agent31Canonical77Exact.championScore
  have hB : 7014 ≤ B :=
    Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014
  apply BB6.Agent11Raw107TwoParent.exact_at_target B hB
    (by
      intro e he
      by_cases hs : sameTable e.2 raw10Parent = true
      · have heq : e.2 = raw10Parent := sameTable_sound hs
        rw [heq]
        exact BB6.Agent13HeldBlockRaw10Combined.raw10_cover_with_cycle_and_halt
          B hB hOpen
      · have hmem : e ∈ otherRoster :=
          List.mem_filter.mpr ⟨he, by simp [otherRoster, hs]⟩
        exact hOther e hmem)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms raw10Parent_in_roster76
#print axioms raw10Parent_exact_member
#print axioms parentEntries_count
#print axioms otherRoster_count
#print axioms exact_from_raw10_remainder_at_champion_score

end BB6.Agent50Canonical76Raw10
