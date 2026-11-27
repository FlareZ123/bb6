import Canonical55Raw106Raw79Graft
import A10Raw83Exact
import Raw85Bound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical53Raw83Raw85Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev p85 : PartialMachine := BB6.Agent21Raw85.parent

theorem p83_count55 :
    (BB6.Agent31Canonical55Raw106Raw79Graft.roster55.filter
      (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem p85_count55 :
    (BB6.Agent31Canonical55Raw106Raw79Graft.roster55.filter
      (fun e => sameTable e.2 p85)).length = 1 := by decide

theorem p83_p85_distinct : sameTable p83 p85 = false := by decide

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p85_root :
    p85 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw85.parent_root

theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem p85_cover : Cover (WeightedBound 6766859) p85 := by
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw85.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ [p83, p85], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact p83_root
  · exact p85_root

theorem parents_cover :
    ∀ p ∈ [p83, p85], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact p83_cover
  · exact p85_cover

noncomputable def roster53 : List (Nat × PartialMachine) :=
  removeParents [p83, p85]
    BB6.Agent31Canonical55Raw106Raw79Graft.roster55

theorem count53 : roster53.length = 53 := by decide

theorem p83_removed :
    (roster53.filter (fun e => sameTable e.2 p83)).length = 0 := by decide

theorem p85_removed :
    (roster53.filter (fun e => sameTable e.2 p85)).length = 0 := by decide

theorem p106_still_removed :
    (roster53.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical55Raw106Raw79Graft.p106)).length = 0 := by decide

theorem p79_still_removed :
    (roster53.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical55Raw106Raw79Graft.p79)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster53, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p83, p85])
    (roster := BB6.Agent31Canonical55Raw106Raw79Graft.roster55)
    BB6.Agent31Canonical55Raw106Raw79Graft.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster53, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster53,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p83_count55
#print axioms p85_count55
#print axioms p83_p85_distinct
#print axioms p83_root
#print axioms p85_root
#print axioms p83_cover
#print axioms p85_cover
#print axioms count53
#print axioms p83_removed
#print axioms p85_removed
#print axioms p106_still_removed
#print axioms p79_still_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical53Raw83Raw85Graft
