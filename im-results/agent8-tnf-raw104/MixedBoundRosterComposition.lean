import RosterCoverComposition

namespace BB6.Agent8MixedBound
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent13RosterComposition

/-- The already closed portion may have a small bound C, while retained
    cylinders must be certified at the proposed global bound B. -/
theorem lifted_roster_dichotomy {C B : Nat} (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hRoot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound B m ∨ ∃ e ∈ roster, compatible e.2 m := by
  intro m hm
  rcases hRoot m hm with h | h
  · exact Or.inl (weightedBound_mono_local hCB h)
  · exact Or.inr h

theorem exact_from_mixed_roster {C B : Nat}
    (hB : 6 ≤ B) (hCB : C ≤ B)
    {roster : List (List Move × PartialMachine)}
    (hRoot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, compatible e.2 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_roster_dichotomy hB (Nat.le_refl B)
    (lifted_roster_dichotomy hCB hRoot) hLeaves champ

theorem exact_from_remaining_roster_at_global_bound (B : Nat) (hB : 395 ≤ B)
    (hLeaves : ∀ e ∈ remainingRootRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_mixed_roster (by omega) hB remainingRootRoster_sound hLeaves champ

#print axioms lifted_roster_dichotomy
#print axioms exact_from_mixed_roster
#print axioms exact_from_remaining_roster_at_global_bound
end BB6.Agent8MixedBound
