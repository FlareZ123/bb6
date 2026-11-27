import Raw59Canonical56AfterRaw124
import Raw106ParentCover
import Raw79ParentCover
import A10Raw83Exact
import Raw85Bound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical52AfterRaw59

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6.Agent31Canonical59Raw113Membership
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent2Canonical56Raw59AfterRaw124.roster56
abbrev p106 : PartialMachine := BB6.Agent10Raw106.p106
abbrev p79 : PartialMachine := BB6.Agent10Raw79.p79
abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev p85 : PartialMachine := BB6.Agent21Raw85.parent

theorem p106_count56 :
    (baseRoster.filter (fun e => sameTable e.2 p106)).length = 1 := by decide

theorem p79_count56 :
    (baseRoster.filter (fun e => sameTable e.2 p79)).length = 1 := by decide

theorem p83_count56 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem p85_count56 :
    (baseRoster.filter (fun e => sameTable e.2 p85)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) [p106, p79, p83, p85] := by
  decide

theorem p106_root :
    p106 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw106.p106_root

theorem p79_root :
    p79 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw79.p79_root

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p85_root :
    p85 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw85.parent_root

theorem p106_cover : Cover (WeightedBound 6766859) p106 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw106.parent_cover.sound m hm k d hk hd)
    (by decide : 253 ≤ 6766859)

theorem p79_cover : Cover (WeightedBound 6766859) p79 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw79.parent_cover.sound m hm k d hk hd)
    (by decide : 2354 ≤ 6766859)

theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem p85_cover : Cover (WeightedBound 6766859) p85 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw85.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ [p106, p79, p83, p85],
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact p106_root
  · exact p79_root
  · exact p83_root
  · exact p85_root

theorem parents_cover :
    ∀ p ∈ [p106, p79, p83, p85],
      Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact p106_cover
  · exact p79_cover
  · exact p83_cover
  · exact p85_cover

noncomputable def roster52 : List (Nat × PartialMachine) :=
  removeParents [p106, p79, p83, p85] baseRoster

theorem count52 : roster52.length = 52 := by decide

theorem all_four_removed :
    ∀ p ∈ [p106, p79, p83, p85],
      (roster52.filter (fun e => sameTable e.2 p)).length = 0 := by
  decide

theorem raw59_still_removed :
    (roster52.filter (fun e => sameTable e.2 p59)).length = 0 := by decide

theorem raw124_still_removed :
    (roster52.filter
      (fun e => sameTable e.2 BB6.Agent2Raw124Canonical58Membership.p124)).length = 0 := by
  decide

theorem raw113_still_removed :
    (roster52.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster52, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p106, p79, p83, p85])
    (roster := baseRoster)
    BB6.Agent2Canonical56Raw59AfterRaw124.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster52, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster52,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p106_count56
#print axioms p79_count56
#print axioms p83_count56
#print axioms p85_count56
#print axioms parents_pairwise_distinct
#print axioms p106_cover
#print axioms p79_cover
#print axioms p83_cover
#print axioms p85_cover
#print axioms count52
#print axioms all_four_removed
#print axioms raw59_still_removed
#print axioms raw124_still_removed
#print axioms raw113_still_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical52AfterRaw59
