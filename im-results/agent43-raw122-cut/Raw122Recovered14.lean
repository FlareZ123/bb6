import Raw122Branch01
import Raw122Branch02
import Raw122Branch03
import Raw122Branch06
import Raw122Branch07
import Raw122Branch08
import Raw122Branch09
import Raw122Branch10
import Raw122Branch11
import Raw122Branch15
import Raw122Branch19
import Raw122Branch20
import Raw122Branch21
import Raw122Branch22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered14
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
abbrev child01 := BB6.Agent43Raw122.child ⟨false,false,1⟩
theorem branch01_empty : partialResiduals child01 BB6.Agent43Raw122.branch01 = [] := by
  rw [BB6.Agent43Raw122.branch01, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child01 (1,true) (some mv)) (BB6.Agent43Raw122.kids01 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover01 (m : Machine) (hm : compatible child01 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child01 BB6.Agent43Raw122.branch01 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch01_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch01_empty] at he
    simp at he
abbrev child02 := BB6.Agent43Raw122.child ⟨false,false,2⟩
theorem branch02_empty : partialResiduals child02 BB6.Agent43Raw122.branch02 = [] := by
  rw [BB6.Agent43Raw122.branch02, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child02 (2,true) (some mv)) (BB6.Agent43Raw122.kids02 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover02 (m : Machine) (hm : compatible child02 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child02 BB6.Agent43Raw122.branch02 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch02_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch02_empty] at he
    simp at he
abbrev child03 := BB6.Agent43Raw122.child ⟨false,false,3⟩
theorem branch03_empty : partialResiduals child03 BB6.Agent43Raw122.branch03 = [] := by
  rw [BB6.Agent43Raw122.branch03, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child03 (4,false) (some mv)) (BB6.Agent43Raw122.kids03 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover03 (m : Machine) (hm : compatible child03 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child03 BB6.Agent43Raw122.branch03 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch03_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch03_empty] at he
    simp at he
abbrev child06 := BB6.Agent43Raw122.child ⟨false,true,0⟩
theorem branch06_empty : partialResiduals child06 BB6.Agent43Raw122.branch06 = [] := by
  rw [BB6.Agent43Raw122.branch06, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child06 (1,true) (some mv)) (BB6.Agent43Raw122.kids06 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover06 (m : Machine) (hm : compatible child06 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child06 BB6.Agent43Raw122.branch06 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch06_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch06_empty] at he
    simp at he
abbrev child07 := BB6.Agent43Raw122.child ⟨false,true,1⟩
theorem branch07_empty : partialResiduals child07 BB6.Agent43Raw122.branch07 = [] := by
  rw [BB6.Agent43Raw122.branch07, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child07 (2,true) (some mv)) (BB6.Agent43Raw122.kids07 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover07 (m : Machine) (hm : compatible child07 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child07 BB6.Agent43Raw122.branch07 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch07_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch07_empty] at he
    simp at he
abbrev child08 := BB6.Agent43Raw122.child ⟨false,true,2⟩
theorem branch08_empty : partialResiduals child08 BB6.Agent43Raw122.branch08 = [] := by
  rw [BB6.Agent43Raw122.branch08, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child08 (4,false) (some mv)) (BB6.Agent43Raw122.kids08 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover08 (m : Machine) (hm : compatible child08 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child08 BB6.Agent43Raw122.branch08 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch08_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch08_empty] at he
    simp at he
abbrev child09 := BB6.Agent43Raw122.child ⟨false,true,3⟩
theorem branch09_empty : partialResiduals child09 BB6.Agent43Raw122.branch09 = [] := by
  exact partialResiduals.eq_2 _ _
theorem cover09 (m : Machine) (hm : compatible child09 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child09 BB6.Agent43Raw122.branch09 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch09_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch09_empty] at he
    simp at he
abbrev child10 := BB6.Agent43Raw122.child ⟨false,true,4⟩
theorem branch10_empty : partialResiduals child10 BB6.Agent43Raw122.branch10 = [] := by
  rw [BB6.Agent43Raw122.branch10, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child10 (4,false) (some mv)) (BB6.Agent43Raw122.kids10 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover10 (m : Machine) (hm : compatible child10 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child10 BB6.Agent43Raw122.branch10 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch10_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch10_empty] at he
    simp at he
abbrev child11 := BB6.Agent43Raw122.child ⟨false,true,5⟩
theorem branch11_empty : partialResiduals child11 BB6.Agent43Raw122.branch11 = [] := by
  rw [BB6.Agent43Raw122.branch11, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child11 (5,false) (some mv)) (BB6.Agent43Raw122.kids11 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover11 (m : Machine) (hm : compatible child11 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child11 BB6.Agent43Raw122.branch11 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch11_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch11_empty] at he
    simp at he
abbrev child15 := BB6.Agent43Raw122.child ⟨true,false,3⟩
theorem branch15_empty : partialResiduals child15 BB6.Agent43Raw122.branch15 = [] := by
  exact partialResiduals.eq_2 _ _
theorem cover15 (m : Machine) (hm : compatible child15 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child15 BB6.Agent43Raw122.branch15 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch15_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch15_empty] at he
    simp at he
abbrev child19 := BB6.Agent43Raw122.child ⟨true,true,1⟩
theorem branch19_empty : partialResiduals child19 BB6.Agent43Raw122.branch19 = [] := by
  rw [BB6.Agent43Raw122.branch19, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child19 (2,true) (some mv)) (BB6.Agent43Raw122.kids19 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover19 (m : Machine) (hm : compatible child19 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child19 BB6.Agent43Raw122.branch19 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch19_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch19_empty] at he
    simp at he
abbrev child20 := BB6.Agent43Raw122.child ⟨true,true,2⟩
theorem branch20_empty : partialResiduals child20 BB6.Agent43Raw122.branch20 = [] := by
  rw [BB6.Agent43Raw122.branch20, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child20 (4,false) (some mv)) (BB6.Agent43Raw122.kids20 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover20 (m : Machine) (hm : compatible child20 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child20 BB6.Agent43Raw122.branch20 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch20_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch20_empty] at he
    simp at he
abbrev child21 := BB6.Agent43Raw122.child ⟨true,true,3⟩
theorem branch21_empty : partialResiduals child21 BB6.Agent43Raw122.branch21 = [] := by
  exact partialResiduals.eq_2 _ _
theorem cover21 (m : Machine) (hm : compatible child21 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child21 BB6.Agent43Raw122.branch21 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch21_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch21_empty] at he
    simp at he
abbrev child22 := BB6.Agent43Raw122.child ⟨true,true,4⟩
theorem branch22_empty : partialResiduals child22 BB6.Agent43Raw122.branch22 = [] := by
  rw [BB6.Agent43Raw122.branch22, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child22 (4,false) (some mv)) (BB6.Agent43Raw122.kids22 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover22 (m : Machine) (hm : compatible child22 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child22 BB6.Agent43Raw122.branch22 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch22_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch22_empty] at he
    simp at he
def kids : Move → PartialAudit := byPartialMove [.unresolved,BB6.Agent43Raw122.branch01,BB6.Agent43Raw122.branch02,BB6.Agent43Raw122.branch03,.unresolved,.unresolved,BB6.Agent43Raw122.branch06,BB6.Agent43Raw122.branch07,BB6.Agent43Raw122.branch08,BB6.Agent43Raw122.branch09,BB6.Agent43Raw122.branch10,BB6.Agent43Raw122.branch11,.unresolved,.unresolved,.unresolved,BB6.Agent43Raw122.branch15,.unresolved,.unresolved,.unresolved,BB6.Agent43Raw122.branch19,BB6.Agent43Raw122.branch20,BB6.Agent43Raw122.branch21,BB6.Agent43Raw122.branch22,.unresolved]
theorem kids_checked (mv : Move) : partialCheck 7014 (BB6.Agent43Raw122.child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · rfl
  · exact BB6.Agent43Raw122.branch06_checked
  · rfl
  · rfl
  · exact BB6.Agent43Raw122.branch01_checked
  · exact BB6.Agent43Raw122.branch07_checked
  · rfl
  · exact BB6.Agent43Raw122.branch19_checked
  · exact BB6.Agent43Raw122.branch02_checked
  · exact BB6.Agent43Raw122.branch08_checked
  · rfl
  · exact BB6.Agent43Raw122.branch20_checked
  · exact BB6.Agent43Raw122.branch03_checked
  · exact BB6.Agent43Raw122.branch09_checked
  · exact BB6.Agent43Raw122.branch15_checked
  · exact BB6.Agent43Raw122.branch21_checked
  · rfl
  · exact BB6.Agent43Raw122.branch10_checked
  · rfl
  · exact BB6.Agent43Raw122.branch22_checked
  · rfl
  · exact BB6.Agent43Raw122.branch11_checked
  · rfl
  · rfl
def tree : PartialAudit := .split 7 (5,true) kids
theorem checked : partialCheck 7014 BB6.Agent43Raw122.parent tree = true := by
  change (zipQueryOK 7014 BB6.Agent43Raw122.parent 7 (5,true) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014 (BB6.Agent43Raw122.child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids_checked⟩
def residuals := partialResiduals BB6.Agent43Raw122.parent tree
def closedIndex (mv : Move) : Bool := ([1, 2, 3, 6, 7, 8, 9, 10, 11, 15, 19, 20, 21, 22] : List Nat).contains (12*mv.write.toNat + 6*mv.right.toNat + mv.next.val)
theorem kids_residuals (mv : Move) : partialResiduals (BB6.Agent43Raw122.child mv) (kids mv) =
    if closedIndex mv then [] else [([], BB6.Agent43Raw122.child mv)] := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · rfl
  · exact branch06_empty
  · rfl
  · rfl
  · exact branch01_empty
  · exact branch07_empty
  · rfl
  · exact branch19_empty
  · exact branch02_empty
  · exact branch08_empty
  · rfl
  · exact branch20_empty
  · exact branch03_empty
  · exact branch09_empty
  · exact branch15_empty
  · exact branch21_empty
  · rfl
  · exact branch10_empty
  · rfl
  · exact branch22_empty
  · rfl
  · exact branch11_empty
  · rfl
  · rfl
theorem residual_count : residuals.length = 10 := by
  rw [residuals,tree,partialResiduals.eq_3,List.length_flatMap]
  simp only [List.length_map,kids_residuals]
  decide
theorem sound : ∀ m, compatible BB6.Agent43Raw122.parent m → WeightedBound 7014 m ∨
      ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 7014 BB6.Agent43Raw122.parent tree BB6.Agent43Raw122.parent_root BB6.Agent43Raw122.parent_nohalt checked
#print axioms sound
#print axioms residual_count
#print axioms cover01
#print axioms cover02
#print axioms cover03
#print axioms cover06
#print axioms cover07
#print axioms cover08
#print axioms cover09
#print axioms cover10
#print axioms cover11
#print axioms cover15
#print axioms cover19
#print axioms cover20
#print axioms cover21
#print axioms cover22
end BB6.Agent43Raw122Recovered14
