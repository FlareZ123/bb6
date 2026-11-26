import Raw39StableIntegrated

namespace BB6.Agent11Raw39Stable
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

abbrev ef := swapStates (4 : Fin 6) 5

theorem support39 : TNFSupport p39 4 := by
  apply refine_support _ _ _ 4 4
  · change TNFSupport (refine (refine (refine root (1,false) (some ⟨true,true,2⟩)) (2,false) (some ⟨false,true,3⟩)) (3,false) (some ⟨true,false,3⟩)) 4
    apply refine_support _ _ _ 4 4
    · apply refine_support _ _ _ 3 4
      · apply refine_support _ _ _ 2 3
        · exact firstOneCylinder_tnf_support
        all_goals decide
      all_goals decide
    all_goals decide
  all_goals decide

theorem childF_to_E (w r : Bool) (m : Machine)
    (hm : compatible (child ⟨w,r,5⟩) m) :
    compatible (child ⟨w,r,4⟩) (renameTable ef m) := by
  have hslot : p39 (0,true) = none := by decide
  obtain ⟨hp,ht⟩ := (compatible_refine_iff p39 m (0,true) hslot _).mp hm
  apply (compatible_refine_iff p39 _ (0,true) hslot _).mpr
  refine ⟨rename_compatible_unused p39 m 4 4 5 (by decide) (by decide) support39 hp, ?_⟩
  change (m (ef.backward 0,true)).map (renameMove ef) = some ⟨w,r,4⟩
  rw [show ef.backward 0=0 by decide, ht]
  rfl

theorem childF_bound (B : Nat) (w r : Bool)
    (h : ∀ m, compatible (child ⟨w,r,4⟩) m → WeightedBound B m)
    (m : Machine) (hm : compatible (child ⟨w,r,5⟩) m) : WeightedBound B m := by
  have hp := ((compatible_refine_iff p39 m (0,true) (by decide) _).mp hm).1
  exact weighted_rename_back B ef m (by decide) (firstOne_terminal p39 p39_root m hp)
    (h _ (childF_to_E w r m hm))

theorem all0RF : ∀ m, compatible (child ⟨false,true,5⟩) m → WeightedBound 944 m :=
  childF_bound 944 false true BB6.Agent11Raw39B0RE.allChild

def tenMoves := residualMoves.filter (· ≠ (⟨false,true,5⟩ : Move))

def sevenMoves : List Move := [⟨false,false,0⟩, ⟨false,false,4⟩, ⟨false,true,2⟩,
  ⟨true,false,0⟩, ⟨true,false,1⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

theorem ten_count : tenMoves.length = 10 := by decide
theorem seven_count : sevenMoves.length = 7 := by decide

theorem cut_ten : ∀ m, compatible p39 m → WeightedBound 1882 m ∨
    ∃ mv ∈ tenMoves, compatible (child mv) m := by
  intro m hm
  rcases cut_integrated m hm with hb | ⟨e,he,hc⟩
  · exact Or.inl hb
  · obtain ⟨mv,hv,rfl⟩ := List.mem_map.mp he
    by_cases hf : mv = ⟨false,true,5⟩
    · subst mv
      exact Or.inl (lift_bound (by decide) (all0RF m hc))
    · exact Or.inr ⟨mv, List.mem_filter.mpr ⟨hv, by simpa using hf⟩,hc⟩

private theorem seven_class (mv : Move) (h : mv ∈ tenMoves) :
    mv ∈ sevenMoves ∨ (mv.next = 5 ∧ ⟨mv.write,mv.right,4⟩ ∈ sevenMoves) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  all_goals first | exact False.elim ((by decide : _ ∉ tenMoves) h) | decide

/-- Seven canonical child bounds suffice to close the complete parent. -/
theorem parent_bound_seven (B : Nat) (hB : 1882 ≤ B)
    (h : ∀ mv ∈ sevenMoves, ∀ m, compatible (child mv) m → WeightedBound B m) :
    ∀ m, compatible p39 m → WeightedBound B m := by
  intro m hm
  rcases cut_ten m hm with hb | ⟨mv,hv,hc⟩
  · exact lift_bound hB hb
  · rcases seven_class mv hv with hs | ⟨hq,hs⟩
    · exact h mv hs m hc
    · rcases mv with ⟨w,r,q⟩
      change q=5 at hq
      subst q
      exact childF_bound B w r (h _ hs) m hc

#print axioms all0RF
#print axioms cut_ten
#print axioms parent_bound_seven
end BB6.Agent11Raw39Stable
