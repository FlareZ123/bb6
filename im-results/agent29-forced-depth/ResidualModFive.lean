import ResidualPeriod
import Lean.Elab.Tactic.Omega
namespace BB6.Agent29Barrier

theorem mod_five_four (n:Nat) (h:(2^n)%5=4) : n%4=2 := by
  have hdiv : 5 ∣ 2^n+1 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hred := reduce_period 5 1 1 n 2 (by decide) (by decide) (by simpa using hdiv)
  have ht : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases ht with h0|h1|h2|h3
  · rw [h0] at hred
    simp at hred
  · rw [h1] at hred
    simp at hred
  · exact h2
  · rw [h3] at hred
    simp at hred

#print axioms mod_five_four
end BB6.Agent29Barrier
