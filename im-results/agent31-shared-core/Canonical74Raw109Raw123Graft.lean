import CanonicalTwoParentRosterOnly
import Raw109Cut
import Raw123Base
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical74Raw109Raw123

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

abbrev p109 : PartialMachine := BB6.Agent4Raw109Cut.parent
abbrev p123 : PartialMachine := BB6.Agent7Raw123.p123
noncomputable def baseRoster := BB6.Agent47CanonicalTwoParent.roster76

/-- Remove the source-accepted Raw109 six-hole parent from the accepted
    canonical76 quotient roster. -/
noncomputable def roster75 :=
  graftRoster p109 [] baseRoster

/-- Independently remove the source-accepted Raw123 parent from the result.
    This composes two cuts against the same stable canonical76 base. -/
noncomputable def roster74 :=
  graftRoster p123 [] roster75

theorem p109_root :
    p109 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem p123_root :
    p123 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent7Raw123.p123_root

/-- The exact parent tables occur once; the sibling obligations are retained. -/
theorem p109_parent_count :
    (baseRoster.filter (fun e => sameTable e.2 p109)).length = 1 := by
  decide

theorem p123_parent_count :
    (roster75.filter (fun e => sameTable e.2 p123)).length = 1 := by
  decide

/-- Both exact cuts remove one distinct quotient representative. -/
theorem count75 : roster75.length = 75 := by
  decide

theorem count74 : roster74.length = 74 := by
  decide

/-- Lift the source-accepted canonical76 dichotomy to the champion score.
    This theorem does not alter or discard any of its 76 quotient obligations. -/
theorem base_sound_at_target :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ baseRoster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound m hm with hb | hr
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr hr

/-- Consume the complete Raw109 parent contract independently of Raw123.
    The only parent-specific premise is its already source-accepted 1703 bound. -/
theorem raw109_sound
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster75, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := p109)
    (replacement := [])
    (roster := baseRoster)
    p109_root
    base_sound_at_target
  intro m hm
  exact Or.inl (fun k d hk hd => Nat.le_trans (h109 m hm k d hk hd) (by decide))

/-- Consume the independent Raw123 Cover after the Raw109 cut. Both parent
    bounds are explicit contracts; neither silently removes its siblings. -/
theorem sound
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster74, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := p123)
    (replacement := [])
    (roster := roster75)
    p123_root
    (raw109_sound h109)
  intro m hm
  exact Or.inl (fun k d hk hd => Nat.le_trans (h123.sound m hm k d hk hd) (by decide))

/-- Conditional exactness at any target B >= the champion score. The two
    accepted parent contracts and all 74 retained Covers remain explicit. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (h109 : ∀ m, compatible p109 m → WeightedBound 1703 m)
    (h123 : Cover (WeightedBound 10000) p123)
    (hLeaves : ∀ e ∈ roster74, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound h109 h123) hLeaves champ

#print axioms p109_root
#print axioms p123_root
#print axioms p109_parent_count
#print axioms p123_parent_count
#print axioms count75
#print axioms count74
#print axioms base_sound_at_target
#print axioms raw109_sound
#print axioms sound
#print axioms exact_at_target

end BB6.Agent31Canonical74Raw109Raw123
