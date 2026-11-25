import Raw10BoxCore
import Root109Membership
import Canonical78Roster

namespace BB6.Agent49BoxBridge
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50RootFrontier
open BB6.Agent49Box BB6.Agent13CrossRouteHeldLeaf109

/-- Consume the exact residual rectangles in the current canonical
    score-B upper bound. Every other quotient entry remains an obligation. -/
theorem exact_from_raw10_remainder (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10Remainder, ∀ m, Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ firstOneB0_1LC → Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47Canonical78.exact_at_target B hB _ champ
  intro e he
  by_cases h : e.2 = firstOneB0_1LC
  · rw [h]
    exact raw10_cover B hB hHeld hOpen
  · exact hOther e he h

#print axioms exact_from_raw10_remainder
end BB6.Agent49BoxBridge
