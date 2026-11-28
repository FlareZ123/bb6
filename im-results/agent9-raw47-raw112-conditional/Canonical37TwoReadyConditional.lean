import Raw39Canonical39Successor

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
A two-parent *conditional* interface on the actual source-accepted Canonical39
roster. The specific Raw47 and Raw112 parents are retained in Canonical39,
in contrast to Raw83/85/106/79/67 already consumed by earlier ancestors.

The theorem proves exact membership and the two-parent sound-removal
reduction 39 -> 37 under two explicit bounded-Cover hypotheses. These Covers
are independently source-certified but are NOT imported into this module;
unconditional Canonical37 requires authentic common-source linking of both.
-/

namespace BB6.Agent9Canonical37TwoReadyConditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39

def p47 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨false, true, 2⟩)
  | _, _ => none

def p112 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 4⟩)
  | 4, true  => some (some ⟨true, false, 2⟩)
  | _, _ => none

abbrev removedParents : List PartialMachine := [p47, p112]

theorem p47_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by
  decide

theorem p112_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) removedParents := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl <;> decide

theorem parents_cover
    (h47 : Cover (WeightedBound 6766859) p47)
    (h112 : Cover (WeightedBound 6766859) p112) :
    ∀ p ∈ removedParents,
      Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact h47
  · exact h112

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem raw47_removed :
    (roster37.filter (fun e => sameTable e.2 p47)).length = 0 := by
  decide

theorem raw112_removed :
    (roster37.filter (fun e => sameTable e.2 p112)).length = 0 := by
  decide

theorem conditional_sound
    (h47 : Cover (WeightedBound 6766859) p47)
    (h112 : Cover (WeightedBound 6766859) p112) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root (parents_cover h47 h112)

theorem conditional_exact_at_champion_score
    (h47 : Cover (WeightedBound 6766859) p47)
    (h112 : Cover (WeightedBound 6766859) p112)
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h47 h112) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p47_count39
#print axioms p112_count39
#print axioms pairwise_distinct
#print axioms parents_root
#print axioms count37
#print axioms raw47_removed
#print axioms raw112_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion_score

end BB6.Agent9Canonical37TwoReadyConditional
