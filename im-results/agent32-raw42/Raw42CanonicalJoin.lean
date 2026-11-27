import Raw42Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42CanonicalJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent32Raw42

def canonical : List Move := retained.filter (fun mv => mv.next.val ≤ 4)
theorem count : canonical.length = 12 := by decide

theorem support : TNFSupport parent 4 := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hv : ∀ q : Fin 6, ∀ b : Bool, ∀ t : Transition,
      parent (q,b) = some t → q.val < 4 ∧
      ∀ mv, t = some mv → mv.next.val < 4 := by decide
  exact hv q b t h

theorem cover (B : Nat) (hB : 12 ≤ B)
    (hc : ∀ mv ∈ canonical, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) parent := by
  have hchild : ∀ mv : Move, mv.next.val ≤ 4 → ∀ m,
      compatible (child mv) m → WeightedBound B m := by
    intro mv hm m h
    cases hd : closed mv with
    | true =>
      intro k d hk hh
      exact Nat.le_trans (closed_sound mv hd m h k d hk hh) hB
    | false =>
      have hr : mv ∈ retained := List.mem_filter.mpr ⟨moves_complete mv,by simp [hd]⟩
      exact (hc mv (List.mem_filter.mpr ⟨hr,by simpa using hm⟩)).sound m h
  apply Cover.leaf parent
  apply tnf_branch_sound B 4 parent (1,true) (by decide) support (by decide) (by decide) parent_root
  · intro m hm k d hk hh
    exact Nat.le_trans (halt_branch m hm k d hk hh) hB
  · intro mv h; exact hchild mv (by omega)
  · intro q h w r; exact hchild ⟨w,r,q⟩ (by simp [h])

#print axioms cover
end BB6.Agent32Raw42CanonicalJoin
