import Raw38Cut
import CanonicalFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw38Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent31FourHoleRoster BB6.Agent19Raw38Cut

theorem parent_member : ∃ e ∈ canonicalRemainingRoster, e.2 = parent := by
  have h : canonicalRemainingRoster.any (fun e => sameTable e.2 parent) = true := by decide
  obtain ⟨e,he,hs⟩ := List.any_eq_true.mp h
  exact ⟨e,he,sameTable_sound hs⟩

/-- Replace the raw38 obligation in any certified quotient roster without
    assuming that its unresolved complement has been discharged. -/
theorem root_cover {C B : Nat} (hCB : C ≤ B) (hB : 395 ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hroot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hOther : ∀ e ∈ roster, sameTable e.2 parent = false → Cover (WeightedBound B) e.2)
    (hResiduals : ∀ e ∈ residuals, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder := by
  apply cover_of_quotient_roster hCB hroot
  intro e he
  cases hs : sameTable e.2 parent with
  | false => exact hOther e he hs
  | true =>
    rw [sameTable_sound hs]
    exact parent_cover hB hResiduals

#print axioms parent_member
#print axioms root_cover
end BB6.Agent19Raw38Roster
