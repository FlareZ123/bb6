import Raw40Partial

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalRefinement BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

noncomputable def refinedRoster := graftRoster parent remaining BB6.Agent47CanonicalRaw114Accepted.roster

theorem refined_count : refinedRoster.length = 379 := by decide

theorem refined_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ refinedRoster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound parent_root BB6.Agent47CanonicalRaw114Accepted.sound local_sound

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ refinedRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB refined_sound hLeaves champ

#print axioms refined_count
#print axioms refined_sound
#print axioms exact_at_target
end BB6.Agent19Raw40
