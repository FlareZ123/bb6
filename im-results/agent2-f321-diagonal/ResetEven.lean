import Phase12
import BulkRuns
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321ResetEven
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk
open BB6.Agent2F321Phase6
open BB6.Agent2F321Phase12

/-- Root-specific second infinite-family exclusion. A reachable middle-even
    reset cannot be followed by an all-high terminal run whose length is
    3 modulo 16. The generic branch arithmetic only forces 3 modulo 4. -/
theorem middleEven_high_terminal_not_mod16_three
    {n k a d A D : Nat}
    (hr : Reach n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1) :
    k % 16 ≠ 3 := by
  intro hk
  have hshape := reachable_middleEven_shape hr h1 hp
  have heq := high_run_terminal_equation hh ht
  have hk3 : 3 ≤ k := by omega
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hk3
  simp [Nat.pow_add, X, Y] at heq
  rcases hshape with hodd | h42
  · by_cases ha : a % 4 = 1
    · omega
    · have ha3 : a % 4 = 3 := by omega
      omega
  · omega

/-- Every middle-even reset followed only by high steps to a terminal gate has
    high-run length 3 modulo 4. -/
theorem middleEven_high_terminal_length_mod4
    {k a A D : Nat}
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1) :
    k % 4 = 3 := by
  have heq := high_run_terminal_equation hh ht
  have hk2 : 2 ≤ k := by
    by_cases h0 : k = 0
    · subst k
      simp [X,Y] at heq
    · by_cases h1 : k = 1
      · subst k
        simp [X,Y] at heq
        omega
      · omega
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hk2
  simp [Nat.pow_add, X, Y] at heq
  omega

/-- Combining the generic mod-4 equation with the root-specific Phase12
    invariant leaves exactly three high-run length classes modulo 16. -/
theorem middleEven_high_terminal_length_mod16_candidates
    {n k a d A D : Nat}
    (hr : Reach n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1) :
    k % 16 = 7 ∨ k % 16 = 11 ∨ k % 16 = 15 := by
  have h4 := middleEven_high_terminal_length_mod4 hh ht
  have hnot := middleEven_high_terminal_not_mod16_three hr h1 h2 hp hh ht
  omega

#print axioms middleEven_high_terminal_not_mod16_three
#print axioms middleEven_high_terminal_length_mod4
#print axioms middleEven_high_terminal_length_mod16_candidates
end BB6.Agent2F321ResetEven
