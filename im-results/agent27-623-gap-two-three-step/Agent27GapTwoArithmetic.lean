import Std
import Lean.Elab.Tactic.Omega
namespace BB6.Agent27GapTwoArithmetic
theorem eight_mul_succ_le_pow (k : Nat) (hk : 4 ≤ k) :
    8*(k+1) ≤ 3^k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases h : 4 ≤ k
      · have hp := ih h
        rw [Nat.pow_succ]
        omega
      · have h4 : k = 3 := by omega
        subst k
        decide
theorem gap_two_output_outside_corridor (a x y : Nat)
    (ha : 32 ≤ a) (hx : x ≤ a/8) (hy : 3*a+2 ≤ y) :
    16*x+24 ≤ y := by omega
theorem gap_two_depth (a : Nat) (ha : 32 ≤ a) : a < 3^(a/8) := by
  have hk : 4 ≤ a/8 := by omega
  have hp := eight_mul_succ_le_pow (a/8) hk
  omega
#print axioms eight_mul_succ_le_pow
#print axioms gap_two_output_outside_corridor
#print axioms gap_two_depth
end BB6.Agent27GapTwoArithmetic
