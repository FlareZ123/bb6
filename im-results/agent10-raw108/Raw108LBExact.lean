import Raw108B0LBData
import FastAuditWeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10Raw108LBExact
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ExactAuditWeight
open BB6.Agent10Raw108B0LB

theorem weight00 : fastWeightCheck 4136175 (child ⟨false,false,0⟩) kid00 = true := by rfl
theorem weight01 : fastWeightCheck 4136175 (child ⟨false,false,1⟩) kid01 = true := by rfl
theorem weight02 : fastWeightCheck 4136175 (child ⟨false,false,2⟩) kid02 = true := by rfl
theorem weight03 : fastWeightCheck 4136175 (child ⟨false,false,3⟩) kid03 = true := by rfl
theorem weight04 : fastWeightCheck 4136175 (child ⟨false,false,4⟩) kid04 = true := by rfl
theorem weight05 : fastWeightCheck 4136175 (child ⟨false,false,5⟩) kid05 = true := by rfl
theorem weight06 : fastWeightCheck 4136175 (child ⟨false,true,0⟩) kid06 = true := by rfl
theorem weight07 : fastWeightCheck 4136175 (child ⟨false,true,1⟩) kid07 = true := by rfl
theorem weight08 : fastWeightCheck 4136175 (child ⟨false,true,2⟩) kid08 = true := by rfl
theorem weight09 : fastWeightCheck 4136175 (child ⟨false,true,3⟩) kid09 = true := by rfl
theorem weight10 : fastWeightCheck 4136175 (child ⟨false,true,4⟩) kid10 = true := by rfl
theorem weight11 : fastWeightCheck 4136175 (child ⟨false,true,5⟩) kid11 = true := by rfl
theorem weight12 : fastWeightCheck 4136175 (child ⟨true,false,0⟩) kid12 = true := by rfl
theorem weight13 : fastWeightCheck 4136175 (child ⟨true,false,1⟩) kid13 = true := by rfl
theorem weight14 : fastWeightCheck 4136175 (child ⟨true,false,2⟩) kid14 = true := by rfl
theorem weight15 : fastWeightCheck 4136175 (child ⟨true,false,3⟩) kid15 = true := by rfl
theorem weight16 : fastWeightCheck 4136175 (child ⟨true,false,4⟩) kid16 = true := by rfl
theorem weight17 : fastWeightCheck 4136175 (child ⟨true,false,5⟩) kid17 = true := by rfl
theorem weight18 : fastWeightCheck 4136175 (child ⟨true,true,0⟩) kid18 = true := by rfl
theorem weight19 : fastWeightCheck 4136175 (child ⟨true,true,1⟩) kid19 = true := by rfl
theorem weight20 : fastWeightCheck 4136175 (child ⟨true,true,2⟩) kid20 = true := by rfl
theorem weight21 : fastWeightCheck 4136175 (child ⟨true,true,3⟩) kid21 = true := by rfl
theorem weight22 : fastWeightCheck 4136175 (child ⟨true,true,4⟩) kid22 = true := by rfl
theorem weight23 : fastWeightCheck 4136175 (child ⟨true,true,5⟩) kid23 = true := by rfl

theorem kids_weight (mv : Move) : fastWeightCheck 4136175 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact weight00
  · exact weight06
  · exact weight12
  · exact weight18
  · exact weight01
  · exact weight07
  · exact weight13
  · exact weight19
  · exact weight02
  · exact weight08
  · exact weight14
  · exact weight20
  · exact weight03
  · exact weight09
  · exact weight15
  · exact weight21
  · exact weight04
  · exact weight10
  · exact weight16
  · exact weight22
  · exact weight05
  · exact weight11
  · exact weight17
  · exact weight23

theorem tree_weight : weightCheck 4136175 parent tree = true := by
  rw [← fastWeightCheck_eq]
  change (fastWeight 4136175 parent 34 (4,false) &&
    allMoves (fun mv => fastWeightCheck 4136175 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨rfl, allMoves_of _ kids_weight⟩

theorem exact_upper : ∀ m, compatible parent m → WeightedBound 4136175 m :=
  (exact_weight_iff parent tree parent_root parent_nohalt
    ((BB6.Agent10Raw108FastAudit.check_eq 4136180 parent tree).symm.trans tree_checked)).mpr tree_weight

#print axioms exact_upper
end BB6.Agent10Raw108LBExact
