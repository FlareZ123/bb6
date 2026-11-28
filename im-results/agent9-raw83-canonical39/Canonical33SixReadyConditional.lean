import Raw39Canonical39Successor

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Six *independently* previously studied complete-parent cylinders tested for
simultaneous exact membership in the currently source-accepted Canonical39
roster. Raw47, Raw112, Raw106, Raw79, Raw83 and Raw85 Covers remain
explicit parameters. This is NOT an unconditional BB(6) bound and is not a
verified roster decrement until source compiled on that exact predecessor.
-/

namespace BB6.Agent9Canonical33SixReadyConditional

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
  | 3, true => some (some ⟨false, true, 2⟩)
  | _, _ => none

def p112 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true => some (some ⟨true, true, 4⟩)
  | 4, true => some (some ⟨true, false, 2⟩)
  | _, _ => none

def p106 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 5⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true => some (some ⟨true, true, 4⟩)
  | 4, true => some (some ⟨false, false, 1⟩)
  | _, _ => none

def p79 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 4⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true => some (some ⟨true, true, 4⟩)
  | 4, true => some (some ⟨false, false, 1⟩)
  | _, _ => none

def p83 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 5⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true => some (some ⟨true, true, 4⟩)
  | 4, true => some (some ⟨false, false, 1⟩)
  | 5, true => some (some ⟨false, true, 0⟩)
  | _, _ => none

def p85 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 5⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true => some (some ⟨true, true, 4⟩)
  | 4, true => some (some ⟨false, false, 1⟩)
  | 5, true => some (some ⟨true, true, 0⟩)
  | _, _ => none

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39

abbrev removedParents : List PartialMachine := [p47, p112, p106, p79, p83, p85]

theorem p47_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by decide

theorem p112_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by decide

theorem p106_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p106)).length = 1 := by decide

theorem p79_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p79)).length = 1 := by decide

theorem p83_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem p85_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p85)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) removedParents := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem parents_cover
    (h0 : Cover (WeightedBound 6766859) p47)
    (h1 : Cover (WeightedBound 6766859) p112)
    (h2 : Cover (WeightedBound 6766859) p106)
    (h3 : Cover (WeightedBound 6766859) p79)
    (h4 : Cover (WeightedBound 6766859) p83)
    (h5 : Cover (WeightedBound 6766859) p85) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

noncomputable def roster33 := removeParents removedParents baseRoster

theorem count33 : roster33.length = 33 := by decide

theorem all_six_removed :
    ∀ p ∈ removedParents,
      (roster33.filter (fun e => sameTable e.2 p)).length = 0 := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem conditional_sound
    (h0 : Cover (WeightedBound 6766859) p47)
    (h1 : Cover (WeightedBound 6766859) p112)
    (h2 : Cover (WeightedBound 6766859) p106)
    (h3 : Cover (WeightedBound 6766859) p79)
    (h4 : Cover (WeightedBound 6766859) p83)
    (h5 : Cover (WeightedBound 6766859) p85) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster33, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root (parents_cover h0 h1 h2 h3 h4 h5)

theorem conditional_exact_at_champion
    (h0 : Cover (WeightedBound 6766859) p47)
    (h1 : Cover (WeightedBound 6766859) p112)
    (h2 : Cover (WeightedBound 6766859) p106)
    (h3 : Cover (WeightedBound 6766859) p79)
    (h4 : Cover (WeightedBound 6766859) p83)
    (h5 : Cover (WeightedBound 6766859) p85)
    (hLeaves : ∀ e ∈ roster33,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h0 h1 h2 h3 h4 h5) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p47_count39
#print axioms p112_count39
#print axioms p106_count39
#print axioms p79_count39
#print axioms p83_count39
#print axioms p85_count39
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms count33
#print axioms all_six_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent9Canonical33SixReadyConditional
