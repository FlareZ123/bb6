import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43TwoRun

private theorem cubic_doubling (n : Nat) (hn : 2≤n) :
    (n+3)^3 ≤ 2*(n+2)^3 := by
  let x := n+2
  have hx : 4≤x := by dsimp [x]; omega
  have hx2 : 4*x ≤ x*x := Nat.mul_le_mul_right x hx
  have hx3 : 4*(x*x) ≤ x*(x*x) := Nat.mul_le_mul_right (x*x) hx
  have hmid : 3*x+1≤x*x := by omega
  have hstep : 3*(x*x)+3*x+1≤x*(x*x) := by omega
  have he : (x+1)^3 = x*(x*x)+3*(x*x)+3*x+1 := by
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    omega
  have hp : x^3=x*(x*x) := by simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  change (n+3)^3≤2*(n+2)^3
  rw [show n+3=x+1 by dsimp [x], show n+2=x by rfl]
  rw [he,hp]
  omega

/-- Uniform cubic-vs-exponential gap, chosen to dominate both shallow sectors. -/
theorem cubic_lt_pow (n : Nat) (hn : 28≤n) :
    8192*(n+2)^3 < 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h28 : 28≤n
    · have hprev := ih h28
      have hdouble := cubic_doubling n (by omega)
      have hh := Nat.mul_le_mul_left 8192 hdouble
      have hgoal : 8192*(n+3)^3 < (2^n)*2 := by omega
      simpa [Nat.succ_eq_add_one, Nat.pow_succ] using hgoal
    · have heq : n=27 := by omega
      subst n
      decide

#print axioms BB6.Agent43TwoRun.cubic_lt_pow
end BB6.Agent43TwoRun