import Root119Shuttle
import Root119EvenExtra

namespace BB6Root119

/-- Complete parity split for any positive finite rightward run of ones
    encountered in D: the odd case shuttles back to F, and the even case
    reaches B just beyond the terminating zero. The hypotheses are on an
    arbitrary tape and do not assert reachability from the blank start. -/
theorem positive_run_parity_dichotomy (m : Nat) (t : Int → Bool) (h : Int)
    (hm : 0 < m)
    (ones : ∀ j : Nat, j < m → t (h+(j:Int)) = true)
    (zero : t (h+(m:Int)) = false) :
    (∃ n : Nat, m = 2*n+1 ∧
       shuttleRun (2*m+1) ⟨.D,h,t⟩ = some ⟨.F,h-1,shuttleFill t h (m+1)⟩)
    ∨ (∃ n : Nat, m = 2*(n+1) ∧
       ∃ u, shuttleRun (m+3) ⟨.D,h,t⟩ = some u ∧
       u.q = .B ∧ u.h = h+m+1) := by
  by_cases he : m%2=0
  · let n := m/2-1
    have hn : m = 2*(n+1) := by dsimp [n]; omega
    have ho : ∀ j : Nat, j < 2*(n+1) → t (h+(j:Int)) = true := by
      intro j hj
      exact ones j (by omega)
    have hz : t (h+(2*(n+1):Int)) = false := by
      have hq : h+(2*(n+1):Int) = h+(m:Int) := by omega
      rw [hq]
      exact zero
    obtain ⟨u,hu,hq,hh⟩ := evenSweep_to_B n t h ho hz
    refine Or.inr ⟨n,hn,u,?_,hq,?_⟩
    · have hs : m+3 = 2*(n+1)+3 := by omega
      rw [hs]
      exact hu
    · dsimp [n] at hh ⊢
      omega
  · let n := m/2
    have hn : m = 2*n+1 := by dsimp [n]; omega
    have ho : ∀ j : Nat, j < 2*n+1 → t (h+(j:Int)) = true := by
      intro j hj
      exact ones j (by omega)
    have hz : t (h+(2*n+1:Int)) = false := by
      have hq : h+(2*n+1:Int) = h+(m:Int) := by omega
      rw [hq]
      exact zero
    have hsh := shuttle n t h ho hz
    refine Or.inl ⟨n,hn,?_⟩
    have ht : 2*m+1 = 4*n+3 := by omega
    have hl : m+1 = 2*n+2 := by omega
    rw [ht,hl]
    exact hsh

#print axioms BB6Root119.positive_run_parity_dichotomy
end BB6Root119
