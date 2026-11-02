import BTraceSource
import Lean.Elab.Tactic.Omega

namespace BB6.BTrace
open BB6.BReduction

/-- Finite versions of the all-one reachability theorem, assuming only k bits. -/
theorem sampled_prefix_reaches (k : Nat)
    (h : ∀ n : Nat, n < k → (sample n).1 = 1) :
    Star (3,0,0) (resetA k,0,0) := by
  induction k with
  | zero =>
      simpa only [resetA] using Star.refl (3,0,0)
  | succ k ih =>
      have hh : ∀ n : Nat, n < k → (sample n).1 = 1 :=
        fun n hn => h n (by omega)
      have hc := cycle (resetA k) 0 0 (by omega)
      have hp : (iterF (resetA k) (0,0)).1 = 1 := h k (by omega)
      have heq :
          (0,(iterF (resetA k) (0,0)).1,(iterF (resetA k) (0,0)).2) =
          (0,1,(sample k).2) := by simp [sample, hp]
      rw [heq] at hc
      have hr : Star (0,1,(sample k).2) (resetA (k+1),0,0) :=
        Star.single (by simp [nextB, resetA, sample])
      exact (ih hh).trans (hc.trans hr)

/-- The original Agent 18 three-counter accelerated machine reaches its fourth reset. -/
theorem original_three_cycles_survive :
    Star (3,0,0) (resetA 3,0,0) := by
  apply sampled_prefix_reaches 3
  intro n hn
  have hs := first_three_samples_odd n hn
  rw [BB6.OneDim.scalarA_eq_resetA n] at hs
  rw [BB6.OneDim.iterG_sample_bit n] at hs
  exact hs

#print axioms sampled_prefix_reaches
#print axioms original_three_cycles_survive
end BB6.BTrace
