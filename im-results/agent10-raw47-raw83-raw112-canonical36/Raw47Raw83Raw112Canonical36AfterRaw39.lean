import Raw39Canonical39Successor
import Raw47KernelBridge
import A10Raw83Exact
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Direct three-parent successor of the source-accepted Raw39 Canonical39 frontier.
Raw47, Raw83, and Raw112 each have independent complete source-accepted parent
Covers.  Once the accepted Raw47 bridge is present in the same authenticated
environment, all three can be removed together, leaving 36 residual Covers.
-/

namespace BB6.Agent10Raw47Raw83Raw112Canonical36AfterRaw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39

abbrev p47 : PartialMachine := BB6.Agent50Raw47Bridge.parent
abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent
abbrev removedParents : List PartialMachine := [p47, p83, p112]

theorem p47_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by
  decide

theorem p83_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by
  decide

theorem p112_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem parents_pairwise :
    sameTable p47 p83 = false ∧
    sameTable p47 p112 = false ∧
    sameTable p83 p112 = false := by
  decide

theorem p47_root :
    p47 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem p83_root :
    p83 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem p47_cover :
    Cover (WeightedBound 6766859) p47 :=
  BB6.Agent50Raw47Bridge.cover_at 6766859 (by omega)

theorem p83_cover :
    Cover (WeightedBound 6766859) p83 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem p112_cover :
    Cover (WeightedBound 6766859) p112 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide : 100000 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | hp
  · exact p47_root
  rcases hp with rfl | rfl
  · exact p83_root
  · exact p112_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | hp
  · exact p47_cover
  rcases hp with rfl | rfl
  · exact p83_cover
  · exact p112_cover

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by
  decide

theorem raw47_removed :
    (roster36.filter (fun e => sameTable e.2 p47)).length = 0 := by
  decide

theorem raw83_removed :
    (roster36.filter (fun e => sameTable e.2 p83)).length = 0 := by
  decide

theorem raw112_removed :
    (roster36.filter (fun e => sameTable e.2 p112)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root parents_cover

theorem sound_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p47_count39
#print axioms p83_count39
#print axioms p112_count39
#print axioms parents_pairwise
#print axioms p47_cover
#print axioms p83_cover
#print axioms p112_cover
#print axioms count36
#print axioms raw47_removed
#print axioms raw83_removed
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms sound_at
#print axioms exact_at_champion_score

end BB6.Agent10Raw47Raw83Raw112Canonical36AfterRaw39
