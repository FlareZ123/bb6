import Raw36Cut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- E and F are both fresh at the C1 split of the six-hole Raw36 branch.
    Consequently one source-certified E child suffices for its F sibling
    at the same weighted bound, with no second generated audit tree. -/
abbrev ef : StatePerm := swapStates (4 : Fin 6) 5

theorem branch_support : TNFSupport branch 4 := by
  apply refine_support _ _ _ 4 4
  · apply refine_support _ _ _ 4 4
    · exact parent_support
    all_goals decide
  all_goals decide

theorem childF_to_E (w r : Bool) (m : Machine)
    (hm : compatible (child ⟨w,r,5⟩) m) :
    compatible (child ⟨w,r,4⟩) (renameTable ef m) := by
  have hslot : branch (2,true) = none := by decide
  obtain ⟨hp,ht⟩ :=
    (compatible_refine_iff branch m (2,true) hslot _).mp hm
  apply (compatible_refine_iff branch _ (2,true) hslot _).mpr
  refine ⟨rename_compatible_unused branch m 4 4 5
    (by decide) (by decide) branch_support hp, ?_⟩
  change (m (ef.backward 2,true)).map (renameMove ef) = some ⟨w,r,4⟩
  rw [show ef.backward (2 : Fin 6) = 2 by decide, ht]
  rfl

theorem childF_bound (B : Nat) (w r : Bool)
    (h : ∀ m, compatible (child ⟨w,r,4⟩) m → WeightedBound B m)
    (m : Machine) (hm : compatible (child ⟨w,r,5⟩) m) :
    WeightedBound B m := by
  have hp :=
    ((compatible_refine_iff branch m (2,true) (by decide) _).mp hm).1
  exact weighted_rename_back B ef m (by decide)
    (firstOne_terminal branch branch_root m hp)
    (h _ (childF_to_E w r m hm))

#print axioms branch_support
#print axioms childF_to_E
#print axioms childF_bound

end BB6.Agent29Raw36
