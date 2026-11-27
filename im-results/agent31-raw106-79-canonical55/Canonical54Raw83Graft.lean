import Canonical55Raw106Raw79Graft
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical54Raw83Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p83 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)

abbrev p83Source : PartialMachine := BB6.Agent10Raw83.parent

theorem p83_count55 :
    (BB6.Agent31Canonical55Raw106Raw79Graft.roster55.filter
      (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem p83_source_eq : p83 = p83Source :=
  sameTable_sound (by decide)

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  rw [p83_source_eq]
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ [p83], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p83_root

theorem parents_cover :
    ∀ p ∈ [p83], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p83_cover

noncomputable def roster54 : List (Nat × PartialMachine) :=
  removeParents [p83] BB6.Agent31Canonical55Raw106Raw79Graft.roster55

theorem count54 : roster54.length = 54 := by decide

theorem p83_removed :
    (roster54.filter (fun e => sameTable e.2 p83)).length = 0 := by decide

theorem p106_still_removed :
    (roster54.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical55Raw106Raw79Graft.p106)).length = 0 := by decide

theorem p79_still_removed :
    (roster54.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical55Raw106Raw79Graft.p79)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster54, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p83])
    (roster := BB6.Agent31Canonical55Raw106Raw79Graft.roster55)
    BB6.Agent31Canonical55Raw106Raw79Graft.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster54, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster54,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p83_count55
#print axioms p83_source_eq
#print axioms p83_root
#print axioms p83_cover
#print axioms count54
#print axioms p83_removed
#print axioms p106_still_removed
#print axioms p79_still_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical54Raw83Graft
