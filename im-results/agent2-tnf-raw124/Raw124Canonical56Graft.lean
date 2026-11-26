import Canonical57Raw112Graft
import Raw124ParentComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124Canonical56Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

/-- Raw124 is the exact first-one parent whose complete Cover is supplied by
    the independent Raw124 parent source audit. -/
abbrev p124 : PartialMachine := BB6.Agent32Raw124ParentJoin.parent124

/-- Raw124 survives exactly once in the accepted Canonical57 candidate list
    obtained after the independent Raw112 delta. -/
theorem p124_count57 :
    (BB6.Agent17Canonical57Raw112Graft.roster57.filter
      (fun e => sameTable e.2 p124)).length = 1 := by decide

theorem p124_root :
    p124 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent32Raw124ParentJoin.root_first

/-- Lift Raw124's source-accepted 4,136,175 Cover to the common
    6,766,859 floor used by the Canonical57 quotient theorem. -/
theorem p124_cover : Cover (WeightedBound 6766859) p124 := by
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent2Raw124ParentComplete.parent_cover.sound m hm k d hk hd)
    (by decide : 4136175 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ [p124], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p124_root

theorem parents_cover :
    ∀ p ∈ [p124], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p124_cover

/-- The 56-entry successor is obtained by removing Raw124 from the actual
    Canonical57Raw112Graft roster, not from a reconstructed roster. -/
noncomputable def roster56 : List (Nat × PartialMachine) :=
  removeParents [p124] BB6.Agent17Canonical57Raw112Graft.roster57

theorem count56 : roster56.length = 56 := by decide

theorem raw59_retained :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = 1 := by decide

theorem raw113_removed :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by decide

theorem raw112_removed :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent17Canonical59Raw112Membership.p112)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster56, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p124])
    (roster := BB6.Agent17Canonical57Raw112Graft.roster57)
    BB6.Agent17Canonical57Raw112Graft.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster56, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster56,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p124_count57
#print axioms p124_root
#print axioms p124_cover
#print axioms count56
#print axioms raw59_retained
#print axioms raw113_removed
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent2Raw124Canonical56Graft
