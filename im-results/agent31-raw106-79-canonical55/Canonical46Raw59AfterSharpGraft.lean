import Canonical47SharpParentsGraft
import Raw59Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical46Raw59AfterSharp

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent31Canonical47SharpParents.roster47
abbrev p59 : PartialMachine := BB6.Agent32Raw59.p59

theorem p59_count47 :
    (baseRoster.filter (fun e => sameTable e.2 p59)).length = 1 := by decide

theorem p59_root :
    p59 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p59_cover : Cover (WeightedBound 6766859) p59 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent32Raw59Exact.bound m hm k d hk hd)
    (by decide : 4136171 ≤ 6766859)

noncomputable def roster46 : List (Nat × PartialMachine) :=
  removeParents [p59] baseRoster

theorem count46 : roster46.length = 46 := by decide

theorem p59_removed :
    (roster46.filter (fun e => sameTable e.2 p59)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster46, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p59]) (roster := baseRoster)
    BB6.Agent31Canonical47SharpParents.sound_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p59_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p59_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster46, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster46,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p59_count47
#print axioms p59_root
#print axioms p59_cover
#print axioms count46
#print axioms p59_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical46Raw59AfterSharp
