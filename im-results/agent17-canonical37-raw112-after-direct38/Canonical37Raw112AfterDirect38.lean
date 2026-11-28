import Canonical38Raw39Raw47Direct
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Serial successor of the source-accepted direct Canonical38 lineage.

The predecessor removes Raw39 and Raw47 from Canonical40.  This module checks
that the independently source-accepted Raw112 parent occurs exactly once in
that exact 38-roster, then removes it at the established global floor.  No
earlier-consumed parent is subtracted again.
-/

namespace BB6.Agent17Canonical37Raw112AfterDirect38

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent3Canonical38Raw39Raw47Direct.roster38

abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent
abbrev removedParents : List PartialMachine := [p112]

theorem p112_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem p112_cover_floor :
    Cover (WeightedBound 6766859) p112 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide : 100000 ≤ 6766859)

theorem raw39_cover_floor :
    Cover (WeightedBound 6766859)
      BB6.Agent11Raw39Raw47Batch38.p39 := by
  simpa only [BB6.Agent11Raw39Raw47Batch38.p39] using
    BB6.Agent11Raw39Canonical40Bridge.weighted_cover
      6766859 (by decide)

theorem raw47_cover_floor :
    Cover (WeightedBound 6766859)
      BB6.Agent11Raw39Raw47Batch38.p47 := by
  change Cover (WeightedBound 6766859)
    BB6.Agent3Canonical38Raw39Raw47Direct.p47
  rw [BB6.Agent3Canonical38Raw39Raw47Direct.raw47_literal_agreement]
  exact BB6.Agent50Raw47Bridge.cover_at 6766859 (by decide)

theorem predecessor_sound :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ baseRoster, TNFQuotientCompatible e.2 m := by
  exact BB6.Agent11Raw39Raw47Batch38.sound38_at
    6766859 (Nat.le_refl _) raw39_cover_floor raw47_cover_floor

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have h : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have h : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_cover_floor

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem raw112_removed :
    (roster37.filter (fun e => sameTable e.2 p112)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    predecessor_sound parents_root parents_cover

theorem sound_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count38
#print axioms p112_cover_floor
#print axioms raw39_cover_floor
#print axioms raw47_cover_floor
#print axioms predecessor_sound
#print axioms count37
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent17Canonical37Raw112AfterDirect38
