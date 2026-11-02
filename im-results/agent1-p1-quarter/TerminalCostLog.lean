import TerminalDyadicBudget

namespace BB6.Agent1Bottleneck

theorem logarithmic_cost_necessity (q m t : Nat)
    (hdeep : 15*q < m+t+1)
    (hdiv : 2^t ≤ 256*q+8*m+76) :
    15*q < m+Nat.log2 (256*q+8*m+76)+1 := by
  have hz : 256*q+8*m+76 ≠ 0 := by omega
  have ht := (Nat.le_log2 hz).mpr hdiv
  omega

theorem pow3_dominates_linear (q : Nat) (hq : 4 ≤ q) :
    352*q+76 < 2^(3*q) := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hprev : 4 ≤ q
    · have hprior := ih hprev
      have hp : 2^(3*(q+1)) = 8*2^(3*q) := by
        have he : 3*(q+1)=3*q+3 := by omega
        rw [he,Nat.pow_add]
        have hc : (2:Nat)^3=8 := by decide
        rw [hc]
        omega
      rw [hp]
      omega
    · have hq3 : q=3 := by omega
      subst q
      decide

theorem twelve_q_cost_barrier (q m t : Nat) (hq : 4≤q)
    (hdeep:15*q < m+t+1)
    (hbudget:2^t ≤256*q+8*m+76) :
    12*q < m := by
  by_cases hm:m ≤ 12*q
  · have ht : 3*q ≤ t := by omega
    have hpow : 2^(3*q) ≤ 2^t := Nat.pow_le_pow_right (by decide:0<(2:Nat)) ht
    have hlin := pow3_dominates_linear q hq
    omega
  · omega

#print axioms logarithmic_cost_necessity
#print axioms pow3_dominates_linear
#print axioms twelve_q_cost_barrier
end BB6.Agent1Bottleneck
