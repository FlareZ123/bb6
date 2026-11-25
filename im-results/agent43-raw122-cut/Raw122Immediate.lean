import Raw122Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def immediate09 : PartialAudit := .closed (.cycle 13 1 false (1))
theorem immediate09_checked : partialCheck 7014 (child ⟨false,true,3⟩) immediate09 = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide

theorem immediate09_sound : ∀ m, compatible (child ⟨false,true,3⟩) m → WeightedBound 7014 m := by
  intro m hm
  have hf : (child ⟨false,true,3⟩) initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hn : weightedTNFNoAssignedHalt (child ⟨false,true,3⟩) := weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt
  rcases partialSound 7014 (child ⟨false,true,3⟩) immediate09 hf hn immediate09_checked m hm with h | ⟨e,he,_⟩
  · exact h
  · have hnil : partialResiduals (child ⟨false,true,3⟩) immediate09 = [] := by decide
    simp [hnil] at he
#print axioms immediate09_sound

def immediate15 : PartialAudit := .closed (.cycle 11 1 false (-1))
theorem immediate15_checked : partialCheck 7014 (child ⟨true,false,3⟩) immediate15 = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide

theorem immediate15_sound : ∀ m, compatible (child ⟨true,false,3⟩) m → WeightedBound 7014 m := by
  intro m hm
  have hf : (child ⟨true,false,3⟩) initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hn : weightedTNFNoAssignedHalt (child ⟨true,false,3⟩) := weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt
  rcases partialSound 7014 (child ⟨true,false,3⟩) immediate15 hf hn immediate15_checked m hm with h | ⟨e,he,_⟩
  · exact h
  · have hnil : partialResiduals (child ⟨true,false,3⟩) immediate15 = [] := by decide
    simp [hnil] at he
#print axioms immediate15_sound

def immediate21 : PartialAudit := .closed (.cycle 4 4 true (1))
theorem immediate21_checked : partialCheck 7014 (child ⟨true,true,3⟩) immediate21 = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide

theorem immediate21_sound : ∀ m, compatible (child ⟨true,true,3⟩) m → WeightedBound 7014 m := by
  intro m hm
  have hf : (child ⟨true,true,3⟩) initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hn : weightedTNFNoAssignedHalt (child ⟨true,true,3⟩) := weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt
  rcases partialSound 7014 (child ⟨true,true,3⟩) immediate21 hf hn immediate21_checked m hm with h | ⟨e,he,_⟩
  · exact h
  · have hnil : partialResiduals (child ⟨true,true,3⟩) immediate21 = [] := by decide
    simp [hnil] at he
#print axioms immediate21_sound

end BB6.Agent43Raw122
