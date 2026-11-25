import HeldBlockConsumer
import CanonicalRaw114Accepted
import Canonical77HeldMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13HeldBlockCanonical77

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent13CrossRouteHeldLeaf109

abbrev Parent : PartialMachine := firstOneB0_1LC

/-- The exact B0=1LC parent survives the accepted raw114 graft as one
    of the current 77 canonical residual obligations. -/
theorem parent_in_roster :
    ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      BB6.Agent31FourHoleRoster.sameTable e.2 Parent = true := by
  simpa [BB6.Agent47CanonicalRaw114Accepted.roster,
    BB6.Agent13Canonical77HeldMembership.canonical77Roster] using
    BB6.Agent13Canonical77HeldMembership.parent_in_canonical77

/-- Exactly one canonical77 entry is the B0=1LC parent. -/
def parentEntries :=
  BB6.Agent47CanonicalRaw114Accepted.roster.filter fun e =>
    BB6.Agent31FourHoleRoster.sameTable e.2 Parent

theorem parentEntries_count : parentEntries.length = 1 := by
  decide

/-- Replacing the one B0=1LC entry leaves 76 other canonical obligations. -/
def otherRoster :=
  BB6.Agent47CanonicalRaw114Accepted.roster.filter fun e =>
    !(BB6.Agent31FourHoleRoster.sameTable e.2 Parent)

theorem otherRoster_count : otherRoster.length = 76 := by
  decide

/-- The exact held block-FAR certificate closes the one-hole source leaf.
    All 65 side-witness cylinders are already consumed by raw10Remainder;
    the explicit complement rectangles remain as separate obligations.
    The 77-way canonical roster therefore reduces to 76 other residuals
    plus the raw10 complement, conditional on those Covers. -/
theorem exact_from_raw10_remainder_77 (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ BB6.Agent49BoxBridge.raw10Remainder,
      ∀ m, BB6.Agent49BoxBridge.Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ Parent → Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47CanonicalRaw114Accepted.exact_at_target B hB ?_ champ
  intro e he
  by_cases h : e.2 = Parent
  · rw [h]
    exact BB6.Agent13HeldBlock.raw10_cover_with_held B hB hOpen
  · exact hOther e he h

#print axioms parent_in_roster
#print axioms parentEntries_count
#print axioms otherRoster_count
#print axioms exact_from_raw10_remainder_77

end BB6.Agent13HeldBlockCanonical77
