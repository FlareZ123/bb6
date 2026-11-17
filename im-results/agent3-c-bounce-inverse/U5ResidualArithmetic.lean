import U5Q0M16Residual
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
Quotient-free arithmetic facts for the U5 residual equation.
This module deliberately imports only the source residual identity;
it contains no M32 finite-quotient certificate or machine transition
model beyond the exact arithmetic equation.
-/

namespace BB6.Agent3U5ResidualArithmetic

private theorem succ_le_two_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpow : 2^(n+1)=2^n*2 := by rw [Nat.pow_succ]
    omega

/-- The residual equations have a solution for every natural w. -/
theorem u5_residual_nonempty (w : Nat) :
    ∃ s m,
      211*s+129=5*2^(201+3360*w) ∧
      32*s=32+840*w+m ∧
      27*w+1≤s ∧ 24*w≤m := by
  let r := 201+3360*w
  have h210 : (2:Nat)^210%211=1 := by decide
  have h201 : (2:Nat)^201%211=68 := by decide
  have h210pow : ((2:Nat)^210)^(16*w)%211=1 := by
    rw [Nat.pow_mod,h210]
    simp
  have hpow : (2:Nat)^r%211=68 := by
    dsimp [r]
    rw [show 201+3360*w=201+210*(16*w) by omega,
      Nat.pow_add,Nat.pow_mul,Nat.mul_mod,h201,h210pow]
  have hmod : (5*2^r)%211=129 := by
    rw [Nat.mul_mod,hpow]
  let s := 5*2^r/211
  have hdecomp := Nat.mod_add_div (5*2^r) 211
  have hs : 211*s+129=5*2^r := by
    dsimp [s]
    rw [hmod] at hdecomp
    omega
  have hrpow : r+1≤2^r := succ_le_two_pow r
  have hlin : 211*(27*w+1)+129≤5*(r+1) := by
    dsimp [r]
    omega
  have hbig : 211*(27*w+1)+129≤5*2^r := by
    calc
      211*(27*w+1)+129 ≤ 5*(r+1) := hlin
      _ ≤ 5*2^r := Nat.mul_le_mul_left 5 hrpow
  have hsge : 27*w+1≤s := by
    dsimp [s]
    omega
  let m := 32*s-32-840*w
  have hmge : 24*w≤m := by
    dsimp [m]
    omega
  have hm : 32*s=32+840*w+m := by
    dsimp [m]
    omega
  exact ⟨s,m,by simpa [r] using hs,hm,hsge,hmge⟩

/-- The residual equation determines s strictly increasingly with w. -/
theorem u5_residual_s_strict_mono
    (w1 w2 s1 s2 : Nat) (hw : w1<w2)
    (hs1 : 211*s1+129=5*2^(201+3360*w1))
    (hs2 : 211*s2+129=5*2^(201+3360*w2)) :
    s1<s2 := by
  have hr : 201+3360*w1 < 201+3360*w2 := by omega
  have hpow : 2^(201+3360*w1) < 2^(201+3360*w2) :=
    Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hr
  omega

/-- The residual equation fixes the authentic root residue class. -/
theorem u5_high_root_parameter_residue (w s : Nat)
    (hs : 211*s+129=5*2^(201+3360*w)) :
    (39+64*s)%32768=18791 ∧ (1+2*s)%1024=587 := by
  have hdiv : 512∣2^(201+3360*w) := by
    change 2^9∣2^(201+3360*w)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpowmod : (2^(201+3360*w))%512=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hmod : (211*s+129)%512=0 := by
    rw [hs,Nat.mul_mod,hpowmod]
  have hsmod : s%512=293 := by omega
  constructor <;> omega

#print axioms u5_residual_nonempty
#print axioms u5_residual_s_strict_mono
#print axioms u5_high_root_parameter_residue

end BB6.Agent3U5ResidualArithmetic
