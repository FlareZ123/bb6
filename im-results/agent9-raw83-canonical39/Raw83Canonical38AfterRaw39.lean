import Raw39Canonical39Successor
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Consume the previously source-accepted exact weighted Raw83 Cover (bound 514)
on the source-accepted Raw39 Canonical39 quotient. This has no dependency on
the current Raw47 or Raw112 source-consumer attempts. It is a distinct
39 -> 38 quotient edge, not an exact BB(6) upper bound.
-/

namespace BB6.Agent9Raw83Canonical38AfterRaw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39
abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev removedParents : List PartialMachine := [p83]

theorem p83_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by
  decide

theorem p83_root :
    p83 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem p83_cover :
    Cover (WeightedBound 6766859) p83 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p83 := by simpa [removedParents] using hp
  subst p
  exact p83_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p83 := by simpa [removedParents] using hp
  subst p
  exact p83_cover

noncomputable def roster38 := removeParents removedParents baseRoster

theorem count38 : roster38.length = 38 := by
  decide

theorem raw83_removed :
    (roster38.filter (fun e => sameTable e.2 p83)).length = 0 := by
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

#print axioms p83_count39
#print axioms p83_cover
#print axioms count38
#print axioms raw83_removed
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent9Raw83Canonical38AfterRaw39
