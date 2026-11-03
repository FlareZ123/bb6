import OneSevenGate
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem four_pow_large (m : Nat) : m+1 ≤ 4^m := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ]
      omega

/-- Every m=16q+7 low Machine C stopping target lies in the
    globally forbidden one-seven fiber (no blank-orbit visitation). -/
theorem low_gate_seven_mod16_unreachable (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (1,2^(2*(16*q+7)+3)-(3*(16*q+7)+4)) := by
  let m : Nat := 16*q+7
  let N : Nat := 2^(2*m+3)
  have hm : 7≤m := by dsimp [m]; omega
  have hpow : N=8*4^m := by
    dsimp [N]
    rw [Nat.pow_add]
    have hdouble : 2^(2*m)=4^m := by
      calc
        2^(2*m) = (2^2)^m := Nat.pow_mul (2:Nat) 2 m
        _ = 4^m := by simp
    rw [hdouble, show (2:Nat)^3=8 by decide]
    ac_rfl
  have hlarge : 3*m+27 ≤ N := by
    have hlinear := four_pow_large m
    rw [hpow]
    omega
  have hdvd : 16 ∣ N := by
    dsimp [N]
    change 2^4 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : N%16=0 := Nat.mod_eq_zero_of_dvd hdvd
  let k : Nat := N-(3*m+4)
  have hk : k+3*m+4=N := by dsimp [k]; omega
  have hklarge : 23≤k := by omega
  have hkmod : k%16=7 := by dsimp [m] at hk hmod ⊢; omega
  let t := k/16
  have ht : 1≤t := by dsimp [t]; omega
  have hkeq : k=16*t+7 := by dsimp [t]; omega
  have hstop := one_seven_blank_unreachable t time ht
  rw [←hkeq] at hstop
  simpa only [m,N,k] using hstop

#print axioms low_gate_seven_mod16_unreachable
end BB6.Agent3
