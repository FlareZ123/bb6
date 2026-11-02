import BTraceFinal
import Agent18BOneDim
import Lean.Elab.Tactic.Omega

namespace BB6.BTrace

theorem source_G_eq (z : Nat) : BB6.OneDim.G z = G z := by rfl

theorem source_iterG_eq (n z : Nat) :
    BB6.OneDim.iterG n z = iterG n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change BB6.OneDim.iterG n (BB6.OneDim.G z) = iterG n (G z)
    rw [source_G_eq z]
    exact ih _

theorem source_scalarA_1 : BB6.OneDim.scalarA 1 = 25 := by decide

theorem source_scalarA_2 : BB6.OneDim.scalarA 2 = 227097 := by decide

theorem source_sample0 :
    (BB6.OneDim.iterG (BB6.OneDim.scalarA 0) 0)%2 = 1 := by
  simpa only [BB6.OneDim.scalarA, source_iterG_eq] using sample0_odd

theorem source_sample1 :
    (BB6.OneDim.iterG (BB6.OneDim.scalarA 1) 0)%2 = 1 := by
  rw [source_scalarA_1, source_iterG_eq]
  exact sample1_odd

theorem source_sample2 :
    (BB6.OneDim.iterG (BB6.OneDim.scalarA 2) 0)%2 = 1 := by
  rw [source_scalarA_2, source_iterG_eq]
  exact third_sample_odd

/-- Every recursively sampled scalar parity bit for cycles 0, 1, 2 is odd. -/
theorem first_three_samples_odd (n : Nat) (hn : n < 3) :
    (BB6.OneDim.iterG (BB6.OneDim.scalarA n) 0)%2 = 1 := by
  have h : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases h with h0 | h1 | h2
  · rw [h0]; exact source_sample0
  · rw [h1]; exact source_sample1
  · rw [h2]; exact source_sample2

#print axioms source_sample2
#print axioms first_three_samples_odd
end BB6.BTrace
