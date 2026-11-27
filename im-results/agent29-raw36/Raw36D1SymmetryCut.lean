import Raw36SymmetryCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47PartialAudit

/-- D1=1LB starts an ordinary first-hole split at B1. The labels
    E and F are still unintroduced and interchangeable. -/
abbrev b1Child (mv : Move) : PartialMachine :=
  refine d1 (1,true) (some mv)

theorem d1_root : d1 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem d1_nohalt : weightedTNFNoAssignedHalt d1 :=
  weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt
theorem d1_support : TNFSupport d1 4 := by
  apply refine_support _ _ _ 4 4 parent_support
  all_goals decide

theorem b1F_to_E (w r : Bool) (m : Machine)
    (hm : compatible (b1Child ⟨w,r,5⟩) m) :
    compatible (b1Child ⟨w,r,4⟩) (renameTable ef m) := by
  have hs : d1 (1,true) = none := by decide
  obtain ⟨hp,ht⟩ :=
    (compatible_refine_iff d1 m (1,true) hs _).mp hm
  apply (compatible_refine_iff d1 _ (1,true) hs _).mpr
  refine ⟨rename_compatible_unused d1 m 4 4 5
    (by decide) (by decide) d1_support hp, ?_⟩
  change (m (ef.backward 1,true)).map (renameMove ef) = some ⟨w,r,4⟩
  rw [show ef.backward (1 : Fin 6) = 1 by decide, ht]
  rfl

theorem b1F_bound (B : Nat) (w r : Bool)
    (h : ∀ m, compatible (b1Child ⟨w,r,4⟩) m → WeightedBound B m)
    (m : Machine) (hm : compatible (b1Child ⟨w,r,5⟩) m) :
    WeightedBound B m := by
  have hp :=
    ((compatible_refine_iff d1 m (1,true) (by decide) _).mp hm).1
  exact weighted_rename_back B ef m (by decide)
    (firstOne_terminal d1 d1_root m hp)
    (h _ (b1F_to_E w r m hm))

/-- Twenty B1 assignments, rather than twenty-four, suffice to bound the
    whole seven-hole Raw36 D1=1LB cylinder. This is independent of any
    candidate-search certificate and covers the true halt assignment too. -/
theorem d1_bound_from_twenty (B : Nat) (hB : 166 ≤ B)
    (h : ∀ mv ∈ representatives, ∀ m,
      compatible (b1Child mv) m → WeightedBound B m)
    (m : Machine) (hm : compatible d1 m) : WeightedBound B m := by
  let t : PartialAudit := .split 6 (1,true) (fun _ => .unresolved)
  have hc : partialCheck 166 d1 t = true := by
    rw [partialCheck.eq_3, Bool.and_eq_true]
    exact ⟨by decide, allMoves_of _ (by intro mv; rfl)⟩
  rcases partialSound 166 d1 t d1_root d1_nohalt hc m hm with hb | ⟨e,he,hh⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · rw [partialResiduals.eq_3] at he
    obtain ⟨mv,_,hmem⟩ := List.mem_flatMap.mp he
    rw [partialResiduals.eq_1] at hmem
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hmem
    have he'' : e' = ([], b1Child mv) := by
      simpa only [List.mem_singleton] using he'
    rw [← heq,he''] at hh
    rcases representative_class mv with hs | ⟨hq,hs⟩
    · exact h mv hs m hh
    · rcases mv with ⟨w,r,q⟩
      change q = 5 at hq
      subst q
      exact b1F_bound B w r (h _ hs) m hh

theorem d1_cover_from_twenty (B : Nat) (hB : 166 ≤ B)
    (h : ∀ mv ∈ representatives, Cover (WeightedBound B) (b1Child mv)) :
    Cover (WeightedBound B) d1 := by
  apply Cover.leaf
  intro m hm
  exact d1_bound_from_twenty B hB
    (by intro mv hmv m hc; exact (h mv hmv).sound m hc) m hm

#print axioms d1_support
#print axioms b1F_to_E
#print axioms d1_bound_from_twenty
#print axioms d1_cover_from_twenty
end BB6.Agent29Raw36
