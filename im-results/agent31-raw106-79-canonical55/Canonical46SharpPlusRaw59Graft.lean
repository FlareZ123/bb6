import Canonical50EightReadyParentsGraft
import SharpRaw95
import Raw103Data
import SharpRaw105
import Raw59Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical46SharpPlusRaw59

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent31Canonical50EightReadyParents.roster50
abbrev p95 : PartialMachine := BB6.Agent3Raw95.p95
abbrev p103 : PartialMachine := BB6.Agent3Raw103.p103
abbrev p105 : PartialMachine := BB6.Agent3Raw105.p105
abbrev p59 : PartialMachine := BB6.Agent32Raw59.p59
abbrev newParents : List PartialMachine := [p95, p103, p105, p59]

theorem p95_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p95)).length = 1 := by decide
theorem p103_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p103)).length = 1 := by decide
theorem p105_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p105)).length = 1 := by decide
theorem p59_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p59)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) newParents := by decide

theorem p95_root : p95 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p103_root : p103 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p105_root : p105 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p59_root : p59 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p95_cover : Cover (WeightedBound 6766859) p95 := by
  apply Cover.leaf
  exact (BB6.Agent31SharpRaw95.exact95 6766859).2
    (by decide : 379 ≤ 6766859)

theorem p103_cover : Cover (WeightedBound 6766859) p103 := by
  apply Cover.leaf
  exact (BB6.Agent3Raw103.exact103 6766859).2
    (by decide : 116 ≤ 6766859)

theorem p105_cover : Cover (WeightedBound 6766859) p105 := by
  apply Cover.leaf
  exact (BB6.Agent31SharpRaw105.exact105 6766859).2
    (by decide : 182 ≤ 6766859)

theorem p59_cover : Cover (WeightedBound 6766859) p59 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent32Raw59Exact.bound m hm k d hk hd)
    (by decide : 4136171 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ newParents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [newParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact p95_root
  · exact p103_root
  · exact p105_root
  · exact p59_root

theorem parents_cover :
    ∀ p ∈ newParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [newParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact p95_cover
  · exact p103_cover
  · exact p105_cover
  · exact p59_cover

noncomputable def roster46 : List (Nat × PartialMachine) :=
  removeParents newParents baseRoster

theorem count46 : roster46.length = 46 := by decide

theorem all_new_parents_removed :
    ∀ p ∈ newParents,
      (roster46.filter (fun e => sameTable e.2 p)).length = 0 := by
  intro p hp
  simp only [newParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster46, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := newParents) (roster := baseRoster)
    BB6.Agent31Canonical50EightReadyParents.sound_integrated
    parents_root parents_cover

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

#print axioms p95_count50
#print axioms p103_count50
#print axioms p105_count50
#print axioms p59_count50
#print axioms parents_pairwise_distinct
#print axioms p95_cover
#print axioms p103_cover
#print axioms p105_cover
#print axioms p59_cover
#print axioms count46
#print axioms all_new_parents_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical46SharpPlusRaw59
