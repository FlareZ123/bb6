import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FourLayer

/-- Quintic exponential separation for the four-remainder argument. -/
theorem quintic_gap_76 (n : Nat) (hn : 76 ≤ n) :
    21120000000000*(n+2)^5 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 81
    · have hc : n=76 ∨ n=77 ∨ n=78 ∨ n=79 ∨ n=80 := by omega
      rcases hc with h|h|h|h|h <;> subst n <;> decide
    · have hnprev : 76 ≤ n-5 := by omega
      have hi := ih (n-5) (by omega) hnprev
      have hlin : n+2 ≤ 2*((n-5)+2) := by omega
      have hg := Nat.pow_le_pow_left hlin 5
      have hpow : (n+2)^5 ≤ 32*((n-5)+2)^5 := by
        calc
          (n+2)^5 ≤ (2*((n-5)+2))^5 := hg
          _ = 32*((n-5)+2)^5 := by
            rw [show (32:Nat)=2*2*2*2*2 by decide]
            simp only [Nat.pow_succ,Nat.pow_zero]
            ac_rfl
      have hscale : 21120000000000*(n+2)^5 ≤
          32*(21120000000000*((n-5)+2)^5) := by
        calc
          21120000000000*(n+2)^5 ≤
              21120000000000*(32*((n-5)+2)^5) :=
            Nat.mul_le_mul_left 21120000000000 hpow
          _ = 32*(21120000000000*((n-5)+2)^5) := by ac_rfl
      have hpow2 : 2^n = 32*2^(n-5) := by
        have he : n=(n-5)+5 := by omega
        rw [he,Nat.pow_add]
        simp [Nat.mul_comm]
      omega

#print axioms quintic_gap_76

end BB6.Agent43FourLayer
