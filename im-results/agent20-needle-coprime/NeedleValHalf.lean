import Init
import Lean.Elab.Tactic.Omega

namespace NeedleValHalf

theorem n_le_two_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ']
    have hp : 0 < (2:Nat)^n := Nat.pow_pos (by decide)
    omega

theorem v_bound (v : Nat) (hv : 2 ≤ v) :
    v ≤ 2^(v-2)+2 := by
  let z := v-2
  have hz : v = z+2 := by dsimp [z]; omega
  have h := n_le_two_pow z
  rw [hz]
  simp only [Nat.add_sub_cancel_right]
  omega

theorem power_shift (v : Nat) (hv : 2 ≤ v) :
    2^v = 4*2^(v-2) := by
  let z := v-2
  have hz : v = z+2 := by dsimp [z]; omega
  rw [hz]
  simp only [Nat.add_sub_cancel_right, Nat.pow_add]
  simp [Nat.mul_comm]

theorem no_large_valuation (q v s : Nat) (hv : s+1 < v) :
    2^v*2^(s+1) ≠ 2^v*(2*q+3)+v+3*(q+1) := by
  intro heq
  have hpos : 0 < 2^v := Nat.pow_pos (by decide)
  have hgap : 2*q+3 < 2^(s+1) := by
    by_cases h : 2*q+3 < 2^(s+1)
    · exact h
    · have hle : 2^v*2^(s+1) ≤ 2^v*(2*q+3) :=
        Nat.mul_le_mul_left _ (Nat.le_of_not_gt h)
      omega
  have hq : q+2 ≤ 2^s := by
    rw [Nat.pow_succ'] at hgap
    omega
  have hsq : 2^s ≤ 2^(v-2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hq' : q+2 ≤ 2^(v-2) := Nat.le_trans hq hsq
  have hv2 : 2 ≤ v := by omega
  have hb := v_bound v hv2
  have he := power_shift v hv2
  have hmul : 2^v*(2*q+4) ≤ 2^v*2^(s+1) :=
    Nat.mul_le_mul_left _ (by omega : 2*q+4 ≤ 2^(s+1))
  have hsmall : 2^v ≤ v+3*(q+1) := by
    rw [heq] at hmul
    have hx : 2^v*(2*q+4) = 2^v*(2*q+3)+2^v := by
      simp [Nat.mul_succ, Nat.add_assoc]
    rw [hx] at hmul
    omega
  omega

/-- Even at the boundary exponent K=2v, the inverse equation is impossible. -/
theorem no_equal_valuation (q v : Nat) (hv : 2 ≤ v) :
    2^v*2^v ≠ 2^v*(2*q+3)+v+3*(q+1) := by
  intro heq
  have hpos : 0 < 2^v := Nat.pow_pos (by decide)
  have hgap : 2*q+3 < 2^v := by
    by_cases h : 2*q+3 < 2^v
    · exact h
    · have hle : 2^v*2^v ≤ 2^v*(2*q+3) :=
        Nat.mul_le_mul_left _ (Nat.le_of_not_gt h)
      omega
  let z := v-1
  have hz : v=z+1 := by dsimp [z]; omega
  have hvpow : (2:Nat)^v=2*2^z := by
    rw [hz, Nat.pow_succ']
  have hq : q+2 ≤ 2^z := by
    rw [hvpow] at hgap
    omega
  have hvbound : v ≤ 2^z+1 := by
    rw [hz]
    have hi := n_le_two_pow z
    omega
  have hupper : v+3*(q+1) < 2*2^v := by
    rw [hvpow]
    omega
  have hplus : 2^v*(2*q+5)=2^v*(2*q+3)+2*2^v := by
    simp [Nat.mul_add, Nat.add_assoc]
    omega
  have hltmul : 2^v*2^v < 2^v*(2*q+5) := by
    rw [hplus, heq]
    omega
  have hlt : 2^v < 2*q+5 := by
    by_cases h : 2^v < 2*q+5
    · exact h
    · have hle : 2^v*(2*q+5) ≤ 2^v*2^v :=
        Nat.mul_le_mul_left _ (Nat.le_of_not_gt h)
      omega
  have hX : 2^v=2*q+4 := by omega
  have heq' : 2^v*(2*q+4) = 2^v*(2*q+3)+v+3*(q+1) := by
    calc
      _ = 2^v*2^v := by rw [hX]
      _ = _ := heq
  have hmul : 2^v*(2*q+4)=2^v*(2*q+3)+2^v := by
    simp [Nat.mul_add, Nat.add_assoc]
    omega
  omega

/-- Each legal predecessor has source valuation at most half its target exponent. -/
theorem predecessor_valuation_twice_le (q v K : Nat)
    (h : 2^v*(2*q+3)+v+3*(q+1)=2^K) : 2*v ≤ K := by
  have hp : 0 < (2:Nat)^v := Nat.pow_pos (by decide)
  have h3 : 3*2^v ≤ 2^v*(2*q+3) := by
    have hh := Nat.mul_le_mul_left (2^v) (show 3 ≤ 2*q+3 by omega)
    simpa [Nat.mul_comm] using hh
  have hk : v+2 ≤ K := by
    by_cases hbad : K ≤ v+1
    · have hpow : (2:Nat)^K ≤ 2^(v+1) :=
        Nat.pow_le_pow_right (by decide) hbad
      have hs : (2:Nat)^(v+1) = 2*2^v := by
        rw [Nat.pow_succ']
      omega
    · omega
  by_cases hbound : 2*v ≤ K
  · exact hbound
  · let s := K-v-1
    have hK : K=v+(s+1) := by dsimp [s]; omega
    have hv : s+1 < v := by dsimp [s]; omega
    have hpow : (2:Nat)^K=2^v*2^(s+1) := by
      rw [hK, Nat.pow_add]
    have heq : 2^v*2^(s+1) = 2^v*(2*q+3)+v+3*(q+1) := by
      rw [← hpow]
      omega
    exact False.elim ((no_large_valuation q v s hv) heq)

/-- All predecessors have valuation strictly below half the terminal exponent. -/
theorem predecessor_valuation_strict (q v K : Nat)
    (h : 2^v*(2*q+3)+v+3*(q+1)=2^K) : 2*v < K := by
  have hle := predecessor_valuation_twice_le q v K h
  by_cases heq : K=2*v
  · have hv : 2 ≤ v := by
      by_cases h0 : v=0
      · subst v
        have hK : K=0 := by omega
        subst K
        simp at h
        omega
      · by_cases h1 : v=1
        · subst v
          have hK : K=2 := by omega
          subst K
          simp at h
          omega
        · omega
    have hp : (2:Nat)^K=2^v*2^v := by
      rw [heq, show 2*v=v+v by omega, Nat.pow_add]
    have bad : 2^v*2^v = 2^v*(2*q+3)+v+3*(q+1) := by
      rw [←hp]
      omega
    exact False.elim ((no_equal_valuation q v hv) bad)
  · omega

/-- The same bound in the exact inverse formula of the published acceleration. -/
theorem source_equation_valuation_strict (q v k : Nat)
    (h : 2^(k+2)+3=(2^(v+1)+3)*(2*q+3)+2*v) :
    2*v<k+1 := by
  have hpowK : (2:Nat)^(k+2)=2*2^(k+1) := by
    rw [show k+2=(k+1)+1 by omega, Nat.pow_succ']
  have hpowV : (2:Nat)^(v+1)=2*2^v := by
    rw [Nat.pow_succ']
  have hExp : 2^v*(2*q+3)+v+3*(q+1)=2^(k+1) := by
    rw [hpowK,hpowV] at h
    have hm : (2*2^v+3)*(2*q+3) =
        2*(2^v*(2*q+3))+3*(2*q+3) := by
      simp [Nat.add_mul, Nat.mul_assoc]
    rw [hm] at h
    omega
  exact predecessor_valuation_strict q v (k+1) hExp

/-- Exact witness attaining 2v+1=K, so the strict bound cannot improve. -/
theorem bound_sharp : 2^6*(2*61+3)+6+3*(61+1)=2^13 := by decide

#print axioms predecessor_valuation_strict
#print axioms source_equation_valuation_strict
#print axioms bound_sharp
end NeedleValHalf
