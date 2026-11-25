import Raw60RootAssembly
import Raw60CanonicalMembership
import Canonical78Roster
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw60CanonicalGraft

open BB6Coverage BB6.Agent13BlankDelay

/-- The four exact child cylinders left open by the raw60 parent audit. -/
def replacement : List (List Move × PartialMachine) :=
  BB6.Agent1Raw60Root.remaining4.map
    (fun mv => ([mv], BB6.Agent1Raw60Root.child mv))

/-- Refine the canonical78 roster by replacing p60 with its four explicit
    residual children. The rest of the canonical roster is preserved. -/
noncomputable def refinedRoster : List (List Move × PartialMachine) :=
  BB6.Agent47CanonicalRefinement.graftRoster
    BB6.Agent1Raw60Root.parent replacement BB6.Agent47Canonical78.roster

/-- If the four residual children are closed at C, remove p60 entirely. -/
noncomputable def closedRoster : List (List Move × PartialMachine) :=
  BB6.Agent47CanonicalRefinement.graftRoster
    BB6.Agent1Raw60Root.parent [] BB6.Agent47Canonical78.roster

theorem parent_in_78 :
    ∃ e ∈ BB6.Agent47Canonical78.roster,
      e.2 = BB6.Agent1Raw60Root.parent :=
  BB6.Agent1Raw60CanonicalMembership.parent_in_78

theorem replacement_length : replacement.length = 4 := by
  decide

theorem refinedRoster_length : refinedRoster.length = 81 := by
  decide

theorem closedRoster_length : closedRoster.length = 77 := by
  decide

/-- Consume the raw60 parent partition without losing its four-child
    complement. This is a root-level consumer, not a local-only audit. -/
theorem refined_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ refinedRoster, BB6.Agent47CanonicalFrontier.TNFQuotientCompatible e.2 m := by
  apply BB6.Agent47CanonicalRefinement.graftRoster_sound
    BB6.Agent1Raw60CanonicalMembership.parent_root_action
    BB6.Agent47Canonical78.roster_sound
  intro m hm
  rcases BB6.Agent1Raw60Root.parent_four_choices m hm with hbound | ⟨mv, hmv, hchild⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hbound k d hk hd) (by decide))
  · exact Or.inr ⟨([mv], BB6.Agent1Raw60Root.child mv),
      List.mem_map.mpr ⟨mv, hmv, rfl⟩, hchild⟩

/-- Four child covers at C close p60 at C. -/
theorem parent_bound_of_four (C : Nat) (hC : 7014 ≤ C)
    (hTail : ∀ mv ∈ BB6.Agent1Raw60Root.remaining4,
      ∀ m, compatible (BB6.Agent1Raw60Root.child mv) m → WeightedBound C m) :
    ∀ m, compatible BB6.Agent1Raw60Root.parent m → WeightedBound C m :=
  BB6.Agent1Raw60Root.parent_scoreB C
    (Nat.le_trans (by decide) hC) hTail

/-- Lift the untouched canonical78 roster to any C >= 7014. -/
theorem base_sound_C (C : Nat) (hC : 7014 ≤ C) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨
        ∃ e ∈ BB6.Agent47Canonical78.roster,
          BB6.Agent47CanonicalFrontier.TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent47Canonical78.roster_sound m hm with hbound | hrest
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hbound k d hk hd) hC)
  · exact Or.inr hrest

/-- Once all four children are bounded, p60 can be removed from the
    canonical78 roster and the remaining 77 representatives still cover
    the authentic root. -/
theorem closed_sound_C (C : Nat) (hC : 7014 ≤ C)
    (hTail : ∀ mv ∈ BB6.Agent1Raw60Root.remaining4,
      ∀ m, compatible (BB6.Agent1Raw60Root.child mv) m → WeightedBound C m) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨
        ∃ e ∈ closedRoster,
          BB6.Agent47CanonicalFrontier.TNFQuotientCompatible e.2 m := by
  apply BB6.Agent47CanonicalRefinement.graftRoster_sound
    BB6.Agent1Raw60CanonicalMembership.parent_root_action
    (base_sound_C C hC)
  intro m hm
  exact Or.inl (parent_bound_of_four C hC hTail m hm)

/-- Conditional exactness interface: the four raw60 child bounds and
    covers for the other 77 roster entries would finish the global proof. -/
theorem exact_at_target {C B : Nat} (hC : 7014 ≤ C) (hCB : C ≤ B)
    (hTail : ∀ mv ∈ BB6.Agent1Raw60Root.remaining4,
      ∀ m, compatible (BB6.Agent1Raw60Root.child mv) m → WeightedBound C m)
    (hLeaves : ∀ e ∈ closedRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent47CanonicalFrontier.exact_from_quotient_roster
    (by omega) hCB (closed_sound_C C hC hTail) hLeaves champ

#print axioms refined_sound
#print axioms parent_bound_of_four
#print axioms closed_sound_C
#print axioms exact_at_target

end BB6.Agent1Raw60CanonicalGraft
