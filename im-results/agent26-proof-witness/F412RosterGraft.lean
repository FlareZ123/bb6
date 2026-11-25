import F412Partition
import Combined109Roster
import MixedBound109Composition
import FourHoleResidualRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Graft
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent47Combined109 BB6.Agent13MixedBound109

theorem fResidualRetained : reducedRoster.any (fun e => sameTable e.2 fResidual) = true := by decide

theorem fResidualUnique :
    (reducedRoster.filter fun e => sameTable e.2 fResidual).length = 1 := by decide

/-- Consume the refined parent at the attained champion score.
    Every one of the other 108 roster obligations is preserved; each of the
    148 unresolved siblings is a separate explicit premise. -/
theorem exactOfF412Graft
    (hclock : HaltsAfter fLiteral fMoves) (hB : fMoves+1 ≤ championScore)
    (hOther : ∀ e ∈ reducedRoster, sameTable e.2 fResidual = false →
      Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ fRemaining,
      Cover (WeightedBound championScore) (fChild e.1 e.2)) :
    BB6.Coverage.ExactBB6 championScore := by
  apply exact_from_reduced_roster_at_champion_score
  intro e he
  cases hs : sameTable e.2 fResidual with
  | false => exact hOther e he hs
  | true =>
    have hEq := sameTable_sound hs
    rw [hEq]
    apply Cover.leaf
    intro m hm
    rcases fResidualSound championScore hB hclock m hm with hb | ⟨r,hr,hc⟩
    · exact hb
    · exact (hLeaves r hr).sound m hc

#print axioms fResidualRetained
#print axioms exactOfF412Graft

end BB6.Agent26F412Graft
