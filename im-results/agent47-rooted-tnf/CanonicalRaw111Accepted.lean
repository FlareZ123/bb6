import CanonicalRaw114Accepted
import Raw111Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47CanonicalRaw111Accepted
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

abbrev p111 := BB6.Agent47Raw111.parent
noncomputable def roster := graftRoster p111 [] BB6.Agent47CanonicalRaw114Accepted.roster
noncomputable def roster75 := graftRoster p111 [] BB6.Agent47CanonicalTwoParent.roster76

theorem parent_bound : ∀ m, compatible p111 m → WeightedBound 7014 m :=
  BB6.Agent47Raw111.all_completions

theorem count : roster.length = 76 := by decide
theorem count75 : roster75.length = 75 := by decide

theorem sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide) BB6.Agent47CanonicalRaw114Accepted.sound
    (fun m hm => Or.inl (parent_bound m hm))

theorem three_parent_sound
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m → WeightedBound 815 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster75, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide) (BB6.Agent47CanonicalRaw114Accepted.two_parent_sound h107)
    (fun m hm => Or.inl (parent_bound m hm))

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m → WeightedBound 815 m)
    (hLeaves : ∀ e ∈ roster75, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (three_parent_sound h107) hLeaves champ

#print axioms parent_bound
#print axioms count
#print axioms count75
#print axioms sound
#print axioms three_parent_sound
#print axioms exact_at_target
end BB6.Agent47CanonicalRaw111Accepted
