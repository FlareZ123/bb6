import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43ThreeLayer

/-- Quartic separation: enough for three nested dyadic remainders. -/
theorem quartic_gap_58 (n : Nat) (hn : 58 ≤ n) :
    13440000000*(n+2)^4 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 62
    · have hc : n=58 ∨ n=59 ∨ n=60 ∨ n=61 := by omega
      rcases hc with h|h|h|h <;> subst n <;> decide
    · have hnprev : 58 ≤ n-4 := by omega
      have hi := ih (n-4) (by omega) hnprev
      have hlin : n+2 ≤ 2*((n-4)+2) := by omega
      have hg := Nat.pow_le_pow_left hlin 4
      have hcube : (n+2)^4 ≤ 16*((n-4)+2)^4 := by
        calc
          (n+2)^4 ≤ (2*((n-4)+2))^4 := hg
          _ = 16*((n-4)+2)^4 := by
            rw [show (16:Nat)=2*2*2*2 by decide]
            simp only [Nat.pow_succ,Nat.pow_zero]
            ac_rfl
      have hscale : 13440000000*(n+2)^4 ≤
          16*(13440000000*((n-4)+2)^4) := by
        calc
          13440000000*(n+2)^4 ≤ 13440000000*(16*((n-4)+2)^4) := Nat.mul_le_mul_left 13440000000 hcube
          _ = 16*(13440000000*((n-4)+2)^4) := by ac_rfl
      have hpow : 2^n=16*2^(n-4) := by
        have he : n=(n-4)+4 := by omega
        rw [he,Nat.pow_add]
        simp [Nat.mul_comm]
      omega

#print axioms quartic_gap_58
end BB6.Agent43ThreeLayer
