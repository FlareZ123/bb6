import Raw42Raw43Canonical35Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Cumulative conditional removal of Raw42, Raw43, then Raw54 from the
authenticated Canonical37 lineage.  All three whole-parent Covers remain
explicit premises.

Raw54 = 1RB---_1RC---_0RD---_1LD0LE_------_------.
-/

namespace BB6.Agent10Raw42Raw43Raw54Canonical34Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p42 : PartialMachine :=
  BB6.Agent10Raw42Raw43Canonical35Conditional.p42
abbrev p43 : PartialMachine :=
  BB6.Agent10Raw42Raw43Canonical35Conditional.p43

def p54 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨false, false, 4⟩)
  | _, _ => none

noncomputable abbrev baseRoster :=
  BB6.Agent10Raw42Raw43Canonical35Conditional.roster35
abbrev removedParents : List PartialMachine := [p54]

theorem p54_count35 :
    (baseRoster.filter (fun e => sameTable e.2 p54)).length = 1 := by
  decide

theorem p54_root :
    p54 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p54 := by simpa [removedParents] using hp
  subst p
  exact p54_root

theorem parents_cover
    (h54 : Cover (WeightedBound 6766859) p54) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p54 := by simpa [removedParents] using hp
  subst p
  exact h54

noncomputable def roster34 := removeParents removedParents baseRoster

theorem count34 : roster34.length = 34 := by
  decide

theorem raw54_removed :
    (roster34.filter (fun e => sameTable e.2 p54)).length = 0 := by
  decide

theorem raw43_remains_removed :
    (roster34.filter (fun e => sameTable e.2 p43)).length = 0 := by
  decide

theorem raw42_remains_removed :
    (roster34.filter (fun e => sameTable e.2 p42)).length = 0 := by
  decide

theorem conditional_sound
    (h42 : Cover (WeightedBound 6766859) p42)
    (h43 : Cover (WeightedBound 6766859) p43)
    (h54 : Cover (WeightedBound 6766859) p54) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster34, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    (BB6.Agent10Raw42Raw43Canonical35Conditional.conditional_sound h42 h43)
    parents_root (parents_cover h54)

theorem conditional_exact_at_champion
    (h42 : Cover (WeightedBound 6766859) p42)
    (h43 : Cover (WeightedBound 6766859) p43)
    (h54 : Cover (WeightedBound 6766859) p54)
    (hLeaves : ∀ e ∈ roster34,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h42 h43 h54) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p54_count35
#print axioms count34
#print axioms raw54_removed
#print axioms raw43_remains_removed
#print axioms raw42_remains_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent10Raw42Raw43Raw54Canonical34Conditional
