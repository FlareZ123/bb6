import Raw39Canonical39Successor
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Unconditional removal of Raw112 from the source-accepted Raw39 Canonical39
frontier. Raw112's source-accepted local Cover is monotone from 100000 to the
global weighted floor 6766859, so the accepted 39-roster reduces to 38.
-/

namespace BB6.Agent10Raw112Canonical38AfterRaw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent
abbrev removedParents : List PartialMachine := [p112]

theorem p112_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem p112_cover :
    Cover (WeightedBound 6766859) p112 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide : 100000 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_cover

noncomputable def roster38 := removeParents removedParents baseRoster

theorem count38 : roster38.length = 38 := by
  decide

theorem raw112_removed :
    (roster38.filter (fun e => sameTable e.2 p112)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root parents_cover

theorem sound_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count39
#print axioms p112_cover
#print axioms count38
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent10Raw112Canonical38AfterRaw39
