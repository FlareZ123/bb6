import CanonicalTwoParentGraft
import Raw114CompleteData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47CanonicalRaw114Accepted
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

abbrev p114 := BB6.Agent47CanonicalTwoParent.p114
noncomputable def roster := graftRoster p114 [] BB6.Agent47Canonical78.roster

theorem parent_bound : ∀ m, compatible p114 m → WeightedBound 7014 m :=
  BB6.Agent47Raw114Complete.raw114_all

theorem count : roster.length = 77 := by decide

theorem sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide) BB6.Agent47Canonical78.roster_sound
    (fun m hm => Or.inl (parent_bound m hm))

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

theorem two_parent_sound
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m → WeightedBound 815 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76, TNFQuotientCompatible e.2 m :=
  BB6.Agent47CanonicalTwoParent.roster76_sound h107 parent_bound

#print axioms parent_bound
#print axioms count
#print axioms sound
#print axioms exact_at_target
#print axioms two_parent_sound
end BB6.Agent47CanonicalRaw114Accepted
