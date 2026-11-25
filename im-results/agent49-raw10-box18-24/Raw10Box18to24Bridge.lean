import Raw10BoxCore
import Box18to24Source
import CanonicalRaw114Accepted
import Canonical77HeldMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Box18to24Bridge

/-- The seven source-checked rectangles are consumed inside the existing
    raw10 parent Cover. Every other raw10 remainder rectangle is retained
    explicitly through the `closedMatch = false` premise. -/
theorem raw10_cover_after_boxes18to24 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m : BB6Coverage.Machine,
      BB6Coverage.compatible BB6.Agent49BoxBridge.held m →
        BB6.Agent13BlankDelay.WeightedBound B m)
    (hRest : ∀ b ∈ BB6.Agent49BoxBridge.raw10Remainder,
      BB6.Agent49Box18to24.closedMatch b = false →
        ∀ m : BB6Coverage.Machine,
          BB6.Agent49Box.Fits b m →
            BB6.Agent13BlankDelay.WeightedBound B m) :
    BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B)
      BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC := by
  exact BB6.Agent49BoxBridge.raw10_cover B hB hHeld
    (fun r hr m hm =>
      BB6.Agent49Box18to24.residual_without_18to24 B (by omega)
        hRest r hr m hm)

/-- The B0=1LC parent is an exact member of the accepted post-raw114
    77-entry roster, not merely a compatible table in the old 78 roster. -/
theorem parent_in_accepted_roster :
    ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 = BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC := by
  obtain ⟨e, he, hsame⟩ :=
    BB6.Agent13Canonical77HeldMembership.parent_in_canonical77
  refine ⟨e, ?_, BB6.Agent31FourHoleRoster.sameTable_sound hsame⟩
  have hRoster :
      BB6.Agent13Canonical77HeldMembership.canonical77Roster =
        BB6.Agent47CanonicalRaw114Accepted.roster := rfl
  rw [← hRoster]
  exact he

/-- Current canonical77 consumer: the seven rectangles at bound 598 are
    closed by rectBound; the exact 27-box complement, held leaf, and all
    other 76 quotient representatives remain explicit hypotheses. -/
theorem exact_from_raw10_boxes18to24 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m : BB6Coverage.Machine,
      BB6Coverage.compatible BB6.Agent49BoxBridge.held m →
        BB6.Agent13BlankDelay.WeightedBound B m)
    (hRest : ∀ b ∈ BB6.Agent49BoxBridge.raw10Remainder,
      BB6.Agent49Box18to24.closedMatch b = false →
        ∀ m : BB6Coverage.Machine,
          BB6.Agent49Box.Fits b m →
            BB6.Agent13BlankDelay.WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC →
        BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47CanonicalRaw114Accepted.exact_at_target B hB ?_ champ
  intro e he
  by_cases h : e.2 = BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC
  · rw [h]
    exact raw10_cover_after_boxes18to24 B hB hHeld hRest
  · exact hOther e he h

#print axioms raw10_cover_after_boxes18to24
#print axioms parent_in_accepted_roster
#print axioms exact_from_raw10_boxes18to24

end BB6.Agent49Box18to24Bridge
