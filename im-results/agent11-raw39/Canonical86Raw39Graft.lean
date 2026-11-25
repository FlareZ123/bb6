import CanonicalTwoParentRosterOnly
import Raw39CombinedPartial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw39Canonical86

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

abbrev p39 : PartialMachine := BB6.Agent11Raw39Combined.p39

/-- Replace the exact Raw39 representative by its eleven checked residuals. -/
noncomputable def roster86 :=
  graftRoster p39 BB6.Agent11Raw39Combined.residuals
    BB6.Agent47CanonicalTwoParent.roster76

theorem parent_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter fun e => sameTable e.2 p39).length = 1 := by
  decide

theorem count : roster86.length = 86 := by
  decide

/-- Lift the accepted 76-residual source theorem to the champion target. -/
theorem base_sound_at_target :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound m hm with hb | hr
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr hr

/-- Conditional 86-residual reduction at the champion score threshold. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨ ∃ e ∈ roster86, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p39)
    (replacement := BB6.Agent11Raw39Combined.residuals)
    (roster := BB6.Agent47CanonicalTwoParent.roster76)
    BB6.Agent11Raw39Combined.p39_root base_sound_at_target
  intro m hm
  rcases BB6.Agent11Raw39Combined.cut_sound m hm with hb | ⟨e, he, hec⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr ⟨e, he, hec⟩

/-- If all eleven new and 75 unchanged quotient cylinders receive Covers,
    the standard champion attainment witness yields exactness. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster86, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms parent_count
#print axioms count
#print axioms base_sound_at_target
#print axioms sound
#print axioms exact_at_target

end BB6.Agent11Raw39Canonical86
