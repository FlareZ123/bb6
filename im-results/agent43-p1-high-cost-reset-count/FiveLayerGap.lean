import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveLayer

/-- Sixth-power exponential separation for five nested shallow remainders. -/
theorem sixth_gap_83 (n : Nat) (hn : 83 ≤ n) :
    19172403734400*(n+2)^6 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 89
    · have hc : n=83 ∨ n=84 ∨ n=85 ∨ n=86 ∨ n=87 ∨ n=88 := by omega
      rcases hc with h|h|h|h|h|h <;> subst n <;> decide
    · have hnprev : 83 ≤ n-6 := by omega
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
      have hscale : 19172403734400*(n+2)^6 ≤
          64*(19172403734400*((n-6)+2)^6) := by
        calc
          19172403734400*(n+2)^6 ≤
              19172403734400*(64*((n-6)+2)^6) :=
            Nat.mul_le_mul_left 19172403734400 hpow6
          _ = 64*(19172403734400*((n-6)+2)^6) := by ac_rfl
      have hpow : 2^n = 64*2^(n-6) := by
        have he : n=(n-6)+6 := by omega
        rw [he,Nat.pow_add]
        simp [Nat.mul_comm]
      omega

#print axioms sixth_gap_83

end BB6.Agent43FiveLayer
