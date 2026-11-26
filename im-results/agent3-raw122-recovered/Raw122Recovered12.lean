import Raw122Branch12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw122Recovered12
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
abbrev child12 := BB6.Agent43Raw122.child ⟨true,false,0⟩
theorem branch12_empty : partialResiduals child12 BB6.Agent43Raw122.branch12 = [] := by
  rw [BB6.Agent43Raw122.branch12, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child12 (0,true) (some mv)) (BB6.Agent43Raw122.kids12 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover12 (m : Machine) (hm : compatible child12 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child12 BB6.Agent43Raw122.branch12 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch12_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch12_empty] at he
    simp at he
#print axioms branch12_empty
#print axioms cover12
end BB6.Agent3Raw122Recovered12
