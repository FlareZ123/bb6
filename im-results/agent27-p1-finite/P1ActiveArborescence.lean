import PosEvenForm
namespace BB6.Agent27Finite
open BB6.Agent1

/-- For each legal nonterminal inverse child, the original P1 counter
transition T returns to its unique G-parent in exactly two steps. The
exception c=1 is precisely the right-five terminal and is excluded. -/
theorem active_inverse_two_step (k c : Nat) (hk : 2 ≤ k) (hc : 3 ≤ c) :
    T (2*k-4) (c+4) = some (2*k-1,c+2) ∧
    T (2*k-1) (c+2) = some (G k c) := by
  have heven : (2*k-4)%2=0 := by omega
  have hodd : (2*k-1)%2=1 := by omega
  have hhalf : (2*k-1)/2+1=k := by omega
  constructor
  · simp [T, heven]
    omega
  · simp [T, hodd, hhalf]
    omega

#print axioms active_inverse_two_step
end BB6.Agent27Finite
