import CanonicalTwoParentRosterOnly

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw58Canonical75

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent31FourHoleRoster BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The exact E1=0RA sibling used by Agent4's Raw58 parent. -/
abbrev p58 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,0⟩)

/-- Remove this one retained representative from the accepted 76-roster. -/
noncomputable def roster75 :=
  graftRoster p58 [] BB6.Agent47CanonicalTwoParent.roster76

theorem parent_count :
    (BB6.Agent47CanonicalTwoParent.roster76.filter fun e => sameTable e.2 p58).length = 1 := by
  decide

theorem count : roster75.length = 75 := by
  decide

/-- Lift the source-accepted 76-residual theorem from 7014 to the champion
    target. The accepted 76 core and its exactness job are explicit inputs. -/
theorem base_sound_at_target :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound m hm with hb | hr
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr hr

/-- Conditional 75-residual reduction. The Raw58 parent premise is at 19310,
    the maximum of its five current child bounds (set by the 1LE leaf 625). -/
theorem sound
    (h58 : ∀ m, compatible p58 m → WeightedBound 19310 m) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster75, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p58) (replacement := [])
    (roster := BB6.Agent47CanonicalTwoParent.roster76)
    (by decide) base_sound_at_target
  intro m hm
  exact Or.inl (fun k d hk hd => Nat.le_trans (h58 m hm k d hk hd) (by decide))

/-- Exactness follows from Covers for the 75 retained representatives and the
    already established champion attainment at the requested target. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (h58 : ∀ m, compatible p58 m → WeightedBound 19310 m)
    (hLeaves : ∀ e ∈ roster75, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound h58) hLeaves champ

#print axioms parent_count
#print axioms count
#print axioms base_sound_at_target
#print axioms sound
#print axioms exact_at_target

end BB6.Agent4Raw58Canonical75
