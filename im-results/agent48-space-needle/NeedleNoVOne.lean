import NeedleTwoStepOdd
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.NeedleTwoStepOdd

/-- Powers of two have only three residues modulo seven. -/
theorem pow_two_mod_seven (k : Nat) :
   2^k%7=1 ∨ 2^k%7=2 ∨ 2^k%7=4 := by
  induction k with
  | zero => left; decide
  | succ k ih =>
    have he : 2^(k+1)%7 = (2^k%7*2)%7 := by
      rw [Nat.pow_succ',Nat.mul_mod]
      simp only [Nat.reduceMod]
      ac_rfl
    rw [he]
    rcases ih with h1|h2|h4
    · right; left; rw [h1]
    · right; right; rw [h2]
    · left; rw [h4]

/-- First-step valuation one cannot feed any odd-ending terminal second step. -/
theorem no_v_one_odd_terminal (q K : Nat) :
    ¬ 2^(K+1)=modulus 1*q+offset 1 := by
  intro h
  have he : 2^(K+1)=35*q+47 := by
    simpa [modulus, den, offset] using h
  have hmod : 2^(K+1)%7=5 := by rw [he]; omega
  rcases pow_two_mod_seven (K+1) with h1|h2|h4
  · omega
  · omega
  · omega

#print axioms pow_two_mod_seven
#print axioms no_v_one_odd_terminal
end BB6.Agent48.NeedleTwoStepOdd
