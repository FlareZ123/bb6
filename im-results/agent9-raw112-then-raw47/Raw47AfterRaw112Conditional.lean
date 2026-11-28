import Raw112Canonical38AfterRaw39

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
A source-gated conditional next edge for the *actually retained* Raw47 root
after consuming the source-certified Raw112 parent on accepted Canonical39.

This file deliberately keeps the Raw47 whole-parent Cover as an explicit
hypothesis; no independent Raw47 proof object is imported. Compilation of
this file must use the original-source accepted Raw112 successor and current
Canonical39 object environment. It is NOT an unconditional 37-Cover result.
-/

namespace BB6.Agent9Raw47AfterRaw112Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent10Raw112Canonical38AfterRaw39.roster38

def p47 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨false, true, 2⟩)
  | _, _ => none

abbrev removedParents : List PartialMachine := [p47]

theorem p47_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by
  decide

theorem p47_root :
    p47 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p47 := by simpa [removedParents] using hp
  subst p
  exact p47_root

theorem parents_cover
    (h47 : Cover (WeightedBound 6766859) p47) :
    ∀ p ∈ removedParents,
      Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p47 := by simpa [removedParents] using hp
  subst p
  exact h47

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem raw47_removed :
    (roster37.filter (fun e => sameTable e.2 p47)).length = 0 := by
  decide

theorem raw112_remains_removed :
    (roster37.filter (fun e =>
      sameTable e.2 BB6.Agent10Raw112Canonical38AfterRaw39.p112)).length = 0 := by
  decide

theorem conditional_sound
    (h47 : Cover (WeightedBound 6766859) p47) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent10Raw112Canonical38AfterRaw39.sound_integrated
    parents_root (parents_cover h47)

theorem conditional_exact_at_champion_score
    (h47 : Cover (WeightedBound 6766859) p47)
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h47) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p47_count38
#print axioms count37
#print axioms raw47_removed
#print axioms raw112_remains_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion_score

end BB6.Agent9Raw47AfterRaw112Conditional
