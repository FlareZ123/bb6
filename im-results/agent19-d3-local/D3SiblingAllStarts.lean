import D3SiblingInvariant
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D3SiblingBoundary

def blankAt (q : Fin 6) : Cfg := ⟨[],false,[],q.val⟩

theorem blankAt_enters (q : Fin 6) : ∃ t ys, run t (blankAt q) = init ys := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := (by decide : ∀ q : Fin 6, q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) q
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨36,List.replicate 7 true,by decide⟩
  · exact ⟨15,List.replicate 3 true,by decide⟩
  · exact ⟨92,List.replicate 13 true,by decide⟩
  · exact ⟨15,List.replicate 3 true,by decide⟩
  · exact ⟨93,List.replicate 13 true,by decide⟩
  · exact ⟨108,List.replicate 9 true ++ false :: List.replicate 6 true,by decide⟩

theorem blankAt_never (q : Fin 6) (n : Nat) : (run n (blankAt q)).st ≠ 6 := by
  obtain ⟨t,ys,hentry⟩ := blankAt_enters q
  intro hh
  by_cases hn : n≤t
  · have he : run t (blankAt q) = run (t-n) (run n (blankAt q)) := by
      rw [← run_add,show n+(t-n)=t by omega]
    rw [frozen_run _ hh,hentry] at he
    exact (by simp [init] : (init ys).st ≠ 6) (he ▸ hh)
  · have he : run n (blankAt q) = run (n-t) (run t (blankAt q)) := by
      rw [← run_add,show t+(n-t)=n by omega]
    rw [hentry] at he
    exact inv_never (n-t) _ (Inv.f ys) (he ▸ hh)

#print axioms blankAt_enters
#print axioms blankAt_never
end D3SiblingBoundary
