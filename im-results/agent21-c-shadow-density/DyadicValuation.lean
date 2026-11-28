import ModularCone

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

private theorem I_succ (b : Nat) : I (b+1)=2*I b := by
  simp [I,P,Nat.pow_succ,Int.mul_comm]

/-- Multiplication by 2 commutes with Euclidean modular reduction
    when the positive modulus is multiplied by 2. -/
theorem double_emod (z d : Int) (hd : 0<d) :
    (2*z)%(2*d)=2*(z%d) := by
  have h0 : 0≤z%d := Int.emod_nonneg _ (by omega : d≠0)
  have h1 : z%d<d := Int.emod_lt_of_pos _ hd
  have hsplit := Int.emod_add_mul_ediv z d
  have hdelta : 2*z-2*(z%d)=2*(d*(z/d)) := by omega
  have hdiv : 2*d∣2*z-2*(z%d) := by
    refine ⟨z/d,?_⟩
    rw [hdelta]
    ac_rfl
  have hcong : (2*z)%(2*d)=(2*(z%d))%(2*d) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      (Int.emod_eq_zero_of_dvd hdiv)
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at hcong
  exact hcong

theorem valuation_le (b : Nat) (z : Int) : valuation b z≤b := by
  induction b generalizing z with
  | zero => simp [valuation]
  | succ b ih =>
      by_cases he : z%2=0
      · simp only [valuation,he,ite_true]
        have h := ih (z/2)
        omega
      · simp only [valuation,he,ite_false]
        omega

/-- The truncated repeated division algorithm reaches exactly b
    iterations iff the signed integer is divisible by 2^b. -/
theorem valuation_full_iff (b : Nat) (z : Int) :
    valuation b z=b ↔ I b∣z := by
  induction b generalizing z with
  | zero => simp [valuation,I,P]
  | succ b ih =>
      have hp := I_succ b
      constructor
      · intro h
        by_cases he : z%2=0
        · have hprev : valuation b (z/2)=b := by
            simp only [valuation,he,ite_true] at h
            omega
          obtain ⟨k,hk⟩ := (ih (z/2)).mp hprev
          refine ⟨k,?_⟩
          rw [hp]
          have hz : z=2*(z/2) := by omega
          rw [hz,hk]
          ac_rfl
        · have hz : valuation (b+1) z=0 := by
            simp only [valuation,he,ite_false]
          omega
      · intro h
        obtain ⟨k,hk⟩ := h
        rw [hp] at hk
        have hz : z=2*(I b*k) := by
          rw [hk]
          ac_rfl
        have he : z%2=0 := by
          rw [hz]
          omega
        have hprev : I b∣z/2 := by
          refine ⟨k,?_⟩
          rw [hz]
          omega
        have hv := (ih (z/2)).mpr hprev
        simp only [valuation,he,ite_true]
        omega

/-- When valuation is below the bit budget, it returns the exact low
    pattern 2^v mod 2^(v+1), including for negative integers. -/
theorem valuation_below (b : Nat) (z : Int)
    (h : valuation b z<b) :
    z%I (valuation b z+1)=I (valuation b z) := by
  induction b generalizing z with
  | zero =>
      simp [valuation] at h
  | succ b ih =>
      by_cases he : z%2=0
      · let t : Int := z/2
        have hv : valuation (b+1) z=1+valuation b t := by
          simp [valuation,he,t]
        have hchild : valuation b t<b := by omega
        have hc := ih t hchild
        have hz : z=2*t := by dsimp [t]; omega
        rw [hv]
        have hp1 : I (1+valuation b t+1)=2*I (valuation b t+1) := by
          rw [show 1+valuation b t+1=valuation b t+1+1 by omega,I_succ]
        have hp0 : I (1+valuation b t)=2*I (valuation b t) := by
          rw [show 1+valuation b t=valuation b t+1 by omega,I_succ]
        rw [hp1,hp0,hz,double_emod t _ (I_pos _),hc]
      · have hv : valuation (b+1) z=0 := by
          simp only [valuation,he,ite_false]
        rw [hv]
        change z%2=1
        omega

/-- The modular checker never spuriously rejects valuation validity:
    the `ValValid` gate fails exactly when the entire available
    low b-bit adjusted sum vanishes. -/
theorem valvalid_iff_not_divisible (b : Nat) (s : Pair) :
    ValValid b s (valuation b (q s)) ↔ ¬I b∣q s := by
  change (valuation b (q s)+1≤b ∧
    q s%I (valuation b (q s)+1)=I (valuation b (q s))) ↔ ¬I b∣q s
  constructor
  · intro h hd
    have hv : valuation b (q s)=b :=
      (valuation_full_iff b (q s)).mpr hd
    omega
  · intro h
    have hle := valuation_le b (q s)
    have hlt : valuation b (q s)<b := by
      by_contra hh
      have hv : valuation b (q s)=b := by omega
      exact h ((valuation_full_iff b (q s)).mp hv)
    exact ⟨by omega,valuation_below b (q s) hlt⟩

#print axioms valvalid_iff_not_divisible
end BB6.Agent21Duality
