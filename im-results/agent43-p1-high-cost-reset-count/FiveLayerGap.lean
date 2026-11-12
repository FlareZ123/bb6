import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveLayer

/-- Sixth-power exponential separation for five nested shallow remainders. -/
theorem sixth_gap_96 (n : Nat) (hn : 96 ≤ n) :
    59136000000000000*(n+2)^6 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 102
    · have hc : n=96 ∨ n=97 ∨ n=98 ∨ n=99 ∨ n=100 ∨ n=101 := by omega
      rcases hc with h|h|h|h|h|h <;> subst n <;> decide
    · have hnprev : 96 ≤ n-6 := by omega
      have hi := ih (n-6) (by omega) hnprev
      have hlin : n+2 ≤ 2*((n-6)+2) := by omega
      have hg := Nat.pow_le_pow_left hlin 6
      have hpow6 : (n+2)^6 ≤ 64*((n-6)+2)^6 := by
        calc
          (n+2)^6 ≤ (2*((n-6)+2))^6 := hg
          _ = 64*((n-6)+2)^6 := by
            rw [show (64:Nat)=2*2*2*2*2*2 by decide]
            simp only [Nat.pow_succ,Nat.pow_zero]
            ac_rfl
      have hscale : 59136000000000000*(n+2)^6 ≤
          64*(59136000000000000*((n-6)+2)^6) := by
        calc
          59136000000000000*(n+2)^6 ≤
              59136000000000000*(64*((n-6)+2)^6) :=
            Nat.mul_le_mul_left 59136000000000000 hpow6
          _ = 64*(59136000000000000*((n-6)+2)^6) := by ac_rfl
      have hpow : 2^n = 64*2^(n-6) := by
        have he : n=(n-6)+6 := by omega
        rw [he,Nat.pow_add]
        simp [Nat.mul_comm]
      omega

#print axioms sixth_gap_96

end BB6.Agent43FiveLayer
