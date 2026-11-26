import Raw122Branch14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122RecoveredLC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
abbrev child14 := BB6.Agent43Raw122.child ⟨true,false,2⟩
theorem branch14_empty : partialResiduals child14 BB6.Agent43Raw122.branch14 = [] := by
  rw [BB6.Agent43Raw122.branch14, partialResiduals.eq_3]
  apply List.flatMap_eq_nil_iff.mpr
  intro mv _
  rw [show partialResiduals (refine child14 (2,true) (some mv)) (BB6.Agent43Raw122.kids14 mv) = [] by
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
    all_goals exact partialResiduals.eq_2 _ _]
  rfl
theorem cover14 (m : Machine) (hm : compatible child14 m) : WeightedBound 7014 m := by
  rcases partialSound 7014 child14 BB6.Agent43Raw122.branch14 (by decide)
      (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) BB6.Agent43Raw122.branch14_checked m hm with h|⟨e,he,_⟩
  · exact h
  · rw [branch14_empty] at he
    simp at he
#print axioms cover14
end BB6.Agent43Raw122RecoveredLC
