import Raw124Canonical58Membership
import Raw106ParentCover
import Raw79ParentCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical55Raw106Raw79Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p106 : PartialMachine := BB6.Agent10Raw106.p106
abbrev p79 : PartialMachine := BB6.Agent10Raw79.p79

theorem p106_count57 :
    (BB6.Agent2Raw124Canonical58Membership.roster57.filter
      (fun e => sameTable e.2 p106)).length = 1 := by decide

theorem p79_count57 :
    (BB6.Agent2Raw124Canonical58Membership.roster57.filter
      (fun e => sameTable e.2 p79)).length = 1 := by decide

theorem p106_p79_distinct : sameTable p106 p79 = false := by decide

theorem p106_root :
    p106 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw106.p106_root

theorem p79_root :
    p79 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw79.p79_root

theorem p106_cover : Cover (WeightedBound 6766859) p106 := by
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw106.parent_cover.sound m hm k d hk hd)
    (by decide : 253 ≤ 6766859)

theorem p79_cover : Cover (WeightedBound 6766859) p79 := by
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw79.parent_cover.sound m hm k d hk hd)
    (by decide : 2354 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ [p106, p79], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact p106_root
  · exact p79_root

theorem parents_cover :
    ∀ p ∈ [p106, p79], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact p106_cover
  · exact p79_cover

noncomputable def roster55 : List (Nat × PartialMachine) :=
  removeParents [p106, p79]
    BB6.Agent2Raw124Canonical58Membership.roster57

theorem count55 : roster55.length = 55 := by decide

theorem p106_removed :
    (roster55.filter (fun e => sameTable e.2 p106)).length = 0 := by decide

theorem p79_removed :
    (roster55.filter (fun e => sameTable e.2 p79)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster55, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p106, p79])
    (roster := BB6.Agent2Raw124Canonical58Membership.roster57)
    BB6.Agent2Raw124Canonical58Membership.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster55, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster55,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p106_count57
#print axioms p79_count57
#print axioms p106_p79_distinct
#print axioms p106_root
#print axioms p79_root
#print axioms p106_cover
#print axioms p79_cover
#print axioms count55
#print axioms p106_removed
#print axioms p79_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical55Raw106Raw79Graft
