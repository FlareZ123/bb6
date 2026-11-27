import Canonical52AfterRaw59Graft
import Raw67ParentCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical51AfterRaw67

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent31Canonical52AfterRaw59.roster52
abbrev p67 : PartialMachine := BB6.Agent10Raw67.p67

theorem p67_count52 :
    (baseRoster.filter (fun e => sameTable e.2 p67)).length = 1 := by decide

theorem p67_root :
    p67 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p67_cover : Cover (WeightedBound 6766859) p67 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw67.parent_cover.sound m hm k d hk hd)
    (by decide : 808 ≤ 6766859)

noncomputable def roster51 : List (Nat × PartialMachine) :=
  removeParents [p67] baseRoster

theorem count51 : roster51.length = 51 := by decide

theorem p67_removed :
    (roster51.filter (fun e => sameTable e.2 p67)).length = 0 := by decide

theorem raw59_still_removed :
    (roster51.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster51, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p67]) (roster := baseRoster)
    BB6.Agent31Canonical52AfterRaw59.sound_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p67_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p67_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster51, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster51,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p67_count52
#print axioms p67_root
#print axioms p67_cover
#print axioms count51
#print axioms p67_removed
#print axioms raw59_still_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical51AfterRaw67
