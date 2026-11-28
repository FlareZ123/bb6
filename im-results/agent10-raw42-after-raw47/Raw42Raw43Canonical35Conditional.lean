import Raw42AfterCanonical37Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Cumulative conditional removal of Raw42 followed by Raw43 from the authenticated
Canonical37 lineage.  Both whole-parent Covers remain explicit premises.

Raw42 = 1RB---_1RC---_0RD---_1LD0LB_------_------
Raw43 = 1RB---_1RC---_0RD---_1LD0RB_------_------
-/

namespace BB6.Agent10Raw42Raw43Canonical35Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p42 : PartialMachine :=
  BB6.Agent10Raw42AfterCanonical37Conditional.p42

def p43 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨false, true, 1⟩)
  | _, _ => none

noncomputable abbrev baseRoster :=
  BB6.Agent10Raw42AfterCanonical37Conditional.roster36
abbrev removedParents : List PartialMachine := [p43]

theorem p43_count36 :
    (baseRoster.filter (fun e => sameTable e.2 p43)).length = 1 := by
  decide

theorem p43_root :
    p43 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact p43_root

theorem parents_cover
    (h43 : Cover (WeightedBound 6766859) p43) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact h43

noncomputable def roster35 := removeParents removedParents baseRoster

theorem count35 : roster35.length = 35 := by
  decide

theorem raw43_removed :
    (roster35.filter (fun e => sameTable e.2 p43)).length = 0 := by
  decide

theorem raw42_remains_removed :
    (roster35.filter (fun e => sameTable e.2 p42)).length = 0 := by
  decide

theorem conditional_sound
    (h42 : Cover (WeightedBound 6766859) p42)
    (h43 : Cover (WeightedBound 6766859) p43) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster35, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    (BB6.Agent10Raw42AfterCanonical37Conditional.conditional_sound h42)
    parents_root (parents_cover h43)

theorem conditional_exact_at_champion
    (h42 : Cover (WeightedBound 6766859) p42)
    (h43 : Cover (WeightedBound 6766859) p43)
    (hLeaves : ∀ e ∈ roster35,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h42 h43) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p43_count36
#print axioms count35
#print axioms raw43_removed
#print axioms raw42_remains_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent10Raw42Raw43Canonical35Conditional
