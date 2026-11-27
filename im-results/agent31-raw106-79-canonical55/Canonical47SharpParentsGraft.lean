import Canonical50EightReadyParentsGraft
import SharpRaw95
import Raw103Data
import SharpRaw105

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical47SharpParents

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent31Canonical50EightReadyParents.roster50
abbrev p95 : PartialMachine := BB6.Agent3Raw95.p95
abbrev p103 : PartialMachine := BB6.Agent3Raw103.p103
abbrev p105 : PartialMachine := BB6.Agent3Raw105.p105
abbrev sharpParents : List PartialMachine := [p95, p103, p105]

theorem p95_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p95)).length = 1 := by decide

theorem p103_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p103)).length = 1 := by decide

theorem p105_count50 :
    (baseRoster.filter (fun e => sameTable e.2 p105)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) sharpParents := by decide

theorem p95_root :
    p95 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p103_root :
    p103 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p105_root :
    p105 initialSlot = some (some ⟨true,true,1⟩) := by decide

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

theorem parents_root :
    ∀ p ∈ sharpParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [sharpParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact p95_root
  · exact p103_root
  · exact p105_root

theorem parents_cover :
    ∀ p ∈ sharpParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [sharpParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact p95_cover
  · exact p103_cover
  · exact p105_cover

noncomputable def roster47 : List (Nat × PartialMachine) :=
  removeParents sharpParents baseRoster

theorem count47 : roster47.length = 47 := by decide

theorem all_sharp_parents_removed :
    ∀ p ∈ sharpParents,
      (roster47.filter (fun e => sameTable e.2 p)).length = 0 := by
  intro p hp
  simp only [sharpParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem raw59_retained :
    (roster47.filter
      (fun e => sameTable e.2 BB6.Agent32Raw59.p59)).length = 1 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster47, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := sharpParents) (roster := baseRoster)
    BB6.Agent31Canonical50EightReadyParents.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster47, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster47,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p95_count50
#print axioms p103_count50
#print axioms p105_count50
#print axioms parents_pairwise_distinct
#print axioms p95_cover
#print axioms p103_cover
#print axioms p105_cover
#print axioms count47
#print axioms all_sharp_parents_removed
#print axioms raw59_retained
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical47SharpParents
