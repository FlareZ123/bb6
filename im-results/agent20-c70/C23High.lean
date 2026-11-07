import C23Rectangle
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C23

private theorem power_linear23 (m : Nat) :
    4*m+4 ≤ (2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_min23 (j m : Nat) (hm : 1≤m) :
    j+3*m+17 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hl := power_linear23 m
  have ht := Nat.mul_le_mul_left 3 hl
  rw [Nat.mul_add]
  omega

/-- An infinite 1-in-128 high stopping-parameter family is removed
    by the one-step source image invariant. No time or counter cutoff. -/
theorem blank_no_high_sum23_right4 (j m k : Nat)
    (hm : 2≤m) (hj : j%4=0)
    (hpair : (j+7)%32=(3*m)%32)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬BB6.Agent3.CReach (2*j+3) k := by
  have hbound := high_min23 j m (by omega)
  have hk12 : 12≤k := by omega
  have hdiv : 32 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^5 ∣ (2:Nat)^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hprod : 32 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    refine ⟨w*(j+3),?_⟩
    rw [hw]
    ac_rfl
  have hmod : (k+j+3*m+5)%32=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod
  have hk4 : k%8=4 := by omega
  have hsum23 : (2*j+3+k)%32=23 := by omega
  exact blank_no_sum23_right4 (2*j+3) k hk12 hk4 hsum23

#print axioms blank_no_high_sum23_right4
end BB6.Agent20C23
