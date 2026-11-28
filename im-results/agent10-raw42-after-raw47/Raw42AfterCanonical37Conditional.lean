import Raw47AfterRaw112Integrated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional Raw42 successor of the authenticated Raw39 -> Raw112 -> Raw47
Canonical37 lineage.  This file proves the exact current-roster geometry and
the 37 -> 36 quotient step while keeping the independent Raw42 parent Cover as
an explicit premise.

Raw42 = 1RB---_1RC---_0RD---_1LD0LB_------_------.
-/

namespace BB6.Agent10Raw42AfterCanonical37Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

def p42 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨false, false, 1⟩)
  | _, _ => none

noncomputable abbrev baseRoster :=
  BB6.Agent17Raw47AfterRaw112Integrated.roster37
abbrev removedParents : List PartialMachine := [p42]

theorem parent_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p42)).length = 1 := by
  decide

theorem parent_root :
    p42 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p42 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover
    (hp : Cover (WeightedBound 6766859) p42) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hmem
  have he : p = p42 := by simpa [removedParents] using hmem
  subst p
  exact hp

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by
  decide

theorem removed_parent_absent :
    (roster36.filter (fun e => sameTable e.2 p42)).length = 0 := by
  decide

theorem conditional_sound
    (hp : Cover (WeightedBound 6766859) p42) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent17Raw47AfterRaw112Integrated.sound_integrated
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound 6766859) p42)
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count37
#print axioms count36
#print axioms removed_parent_absent
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent10Raw42AfterCanonical37Conditional
