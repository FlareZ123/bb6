import Raw39Canonical39Successor

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional joint deletion from the *accepted* Canonical39 roster.
All three parents have independently source-accepted Covers, but their
original-source proof objects must still be authenticated into one shared
source environment. This file has not been source-compiled as of staging.
It deliberately keeps Covers explicit rather than inferring completeness
from independent canonical-frontier counts.
-/

namespace BB6.Agent9Canonical36ThreeParentsConditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

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

def p83 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨true, false, 5⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 4⟩)
  | 4, true  => some (some ⟨false, false, 1⟩)
  | 5, true  => some (some ⟨false, true, 0⟩)
  | _, _ => none

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39
abbrev removedParents : List PartialMachine := [p47, p112, p83]

theorem p47_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by decide

theorem p112_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by decide

theorem p83_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem parents_cover
    (h47 : Cover (WeightedBound 6766859) p47)
    (h112 : Cover (WeightedBound 6766859) p112)
    (h83 : Cover (WeightedBound 6766859) p83) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact h47
  · exact h112
  · exact h83

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by decide

theorem removed_p47 :
    (roster36.filter (fun e => sameTable e.2 p47)).length = 0 := by decide

theorem removed_p112 :
    (roster36.filter (fun e => sameTable e.2 p112)).length = 0 := by decide

theorem removed_p83 :
    (roster36.filter (fun e => sameTable e.2 p83)).length = 0 := by decide

theorem conditional_sound
    (h47 : Cover (WeightedBound 6766859) p47)
    (h112 : Cover (WeightedBound 6766859) p112)
    (h83 : Cover (WeightedBound 6766859) p83) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root (parents_cover h47 h112 h83)

theorem conditional_exact_at_champion
    (h47 : Cover (WeightedBound 6766859) p47)
    (h112 : Cover (WeightedBound 6766859) p112)
    (h83 : Cover (WeightedBound 6766859) p83)
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h47 h112 h83) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p47_count39
#print axioms p112_count39
#print axioms p83_count39
#print axioms count36
#print axioms removed_p47
#print axioms removed_p112
#print axioms removed_p83
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent9Canonical36ThreeParentsConditional
