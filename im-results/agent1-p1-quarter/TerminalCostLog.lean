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

theorem pow1_dominates_linear (q : Nat) (hq : 13 ≤ q) :
    368*q+76 < 2^q := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hprev : 13 ≤ q
    · have hprior:=ih hprev
      have hp:2^(q+1)=2*2^q := by rw [Nat.pow_succ]; omega
      rw [hp]
      omega
    · have hq12:q=12:=by omega
      subst q
      decide

theorem fourteen_q_cost_barrier (q m t : Nat) (hq : 13≤q)
    (hdeep:15*q < m+t+1)
    (hbudget:2^t ≤256*q+8*m+76) :
    14*q < m := by
  by_cases hm:m ≤14*q
  · have ht:q≤t := by omega
    have hp:2^q ≤ 2^t := Nat.pow_le_pow_right (by decide:0<(2:Nat)) ht
    have hbig:=pow1_dominates_linear q hq
    omega
  · omega

#print axioms pow1_dominates_linear
#print axioms fourteen_q_cost_barrier

open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot

/-- Exact source connected trade-off: possible reachable leaf requires
an all-odd inverse cost within a logarithm of 15q. -/
theorem reachable_terminal_log_cost
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=0) (hk : 2 ≤ k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    15*q < m+Nat.log2 (256*q+8*m+76)+1 := by
  obtain ⟨hdeep,_,hbudget⟩ := reachable_terminal_three_gates q b d m t k c root hq hcone hb hb4 hd hi hc hk hr
  exact logarithmic_cost_necessity q m t hdeep hbudget

/-- All potentially blank-reachable even exits from the deep critical
cones require more than 12q prior odd inverse cost when q≥4. -/
theorem reachable_terminal_over_twelve_q
    (q b d m t k c : Nat) (root : Bool)
    (hq : 4 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=0) (hk : 2 ≤ k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    12*q < m := by
  have hq1 : 1≤q := by omega
  obtain ⟨hdeep,_,hbudget⟩ := reachable_terminal_three_gates q b d m t k c root hq1 hcone hb hb4 hd hi hc hk hr
  exact twelve_q_cost_barrier q m t hq hdeep hbudget

/-- Deep-length necessity at q≥13: an authentic even leaf would require
strictly more than 14q odd inverse cost before its final branch. -/
theorem reachable_terminal_over_fourteen_q
    (q b d m t k c : Nat) (root : Bool)
    (hq : 13 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c%2=0) (hk : 2 ≤ k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    14*q < m := by
  have hq1 : 1≤q := by omega
  obtain ⟨hdeep,_,hbudget⟩ := reachable_terminal_three_gates q b d m t k c root hq1 hcone hb hb4 hd hi hc hk hr
  exact fourteen_q_cost_barrier q m t hq hdeep hbudget

#print axioms reachable_terminal_over_fourteen_q

#print axioms reachable_terminal_log_cost
#print axioms reachable_terminal_over_twelve_q

#print axioms logarithmic_cost_necessity
#print axioms pow3_dominates_linear
#print axioms twelve_q_cost_barrier
end BB6.Agent1Bottleneck
