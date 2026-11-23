import EvenOddLowStopPowerGap
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowFanDivisor
open BB6.Agent46

/-- If a number Q differs by a strictly smaller positive term 4C from a
    multiple of 2^t, divisibility by 2^(n+2) forces 2^n to divide C.
    This is the exact source arithmetic that turns the huge halt-target
    exponent into a SMALL divisibility parameter in the index z. -/
theorem subtract_small_power_divisor
    (t n A Q C : Nat)
    (hpos : 0<C) (hsmall : 4*C < 2^t)
    (hEq : Q+4*C=A*2^t)
    (hDiv : 2^(n+2) ∣ Q) :
    2^n ∣ C := by
  have hlt : n+2<t := by
    by_cases hh : n+2<t
    · exact hh
    have hle : t≤n+2 := by omega
    have hpow : 2^t ∣ 2^(n+2) := Nat.pow_dvd_pow 2 hle
    have hqdiv : 2^t ∣ Q := by
      obtain ⟨v,hv⟩ := hpow
      obtain ⟨w,hw⟩ := hDiv
      refine ⟨v*w,?_⟩
      rw [hw,hv]
      ac_rfl
    have htotal : 2^t ∣ A*2^t := by
      refine ⟨A,?_⟩
      ac_rfl
    have hsub : 2^t ∣ A*2^t-Q := Nat.dvd_sub htotal hqdiv
    have he : A*2^t-Q = 4*C := by omega
    rw [he] at hsub
    have hlarge : 2^t ≤ 4*C := Nat.le_of_dvd (by omega) hsub
    omega
  have hdPow : 2^(n+2) ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
  have hdTotal : 2^(n+2) ∣ A*2^t := by
    obtain ⟨v,hv⟩ := hdPow
    refine ⟨A*v,?_⟩
    rw [hv]
    ac_rfl
  have hsub : 2^(n+2) ∣ A*2^t-Q := Nat.dvd_sub hdTotal hDiv
  have he : A*2^t-Q = 4*C := by omega
  rw [he] at hsub
  have hePow : 2^(n+2)=4*2^n := by
    rw [show n+2 = 2+n by omega,Nat.pow_add]
  rw [hePow] at hsub
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0<4) hsub

/-- Exact divisibility transport through a high power with a strictly
    smaller nonzero correction. It holds at EVERY exponent n, including
    values above the high-power exponent, where both sides are false. -/
theorem subtract_small_power_divisor_iff
    (t n A Q C : Nat)
    (hpos : 0<C) (hsmall : 4*C < 2^t)
    (hEq : Q+4*C=A*2^t) :
    (2^(n+2) ∣ Q) ↔ (2^n ∣ C) := by
  constructor
  · exact subtract_small_power_divisor t n A Q C hpos hsmall hEq
  · intro hdivC
    have hpower : 2^n ≤ C := Nat.le_of_dvd hpos hdivC
    have hePow : 2^(n+2)=4*2^n := by
      rw [show n+2=2+n by omega,Nat.pow_add]
    have hlin : 2^(n+2) ≤ 4*C := by omega
    have hlt : n+2 < t := by
      by_cases hh : n+2<t
      · exact hh
      have hge : t≤n+2 := by omega
      have hmon : 2^t ≤ 2^(n+2) :=
        Nat.pow_le_pow_right (by omega) hge
      omega
    have hdPow : 2^(n+2) ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
    have hdTotal : 2^(n+2) ∣ A*2^t := by
      obtain ⟨v,hv⟩ := hdPow
      refine ⟨A*v,?_⟩
      rw [hv]
      ac_rfl
    have hdiv4 : 2^(n+2) ∣ 4*C := by
      obtain ⟨v,hv⟩ := hdivC
      refine ⟨v,?_⟩
      rw [hePow,hv]
      ac_rfl
    have hsub : 2^(n+2) ∣ A*2^t-4*C := Nat.dvd_sub hdTotal hdiv4
    have he : A*2^t-4*C=Q := by omega
    rwa [he] at hsub

private theorem linear_le_power (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- A uniform necessary condition for ANY potential original-section
    low-stop inverse-parent dyadic factor: the depth power divides the
    much smaller linear quantity 519z+73, never an arbitrary power of
    the giant stopping exponent. -/
theorem low_mass_divisor (z u n : Nat)
    (hu : u+6*z+1=2^(1024*z+129))
    (hdiv : 2^(n+2) ∣ 346*u+54) :
    2^n ∣ 519*z+73 := by
  let t := 1024*z+129
  let s := 1024*z+127
  have hlin : s+1 ≤ 2^s := linear_le_power s
  have hC : 519*z+73 < 2^s := by
    dsimp [s] at *
    omega
  have ht : t=s+2 := by dsimp [t,s]
  have htpow : 2^t=4*2^s := by
    rw [ht,Nat.pow_add]
    omega
  have hsmall : 4*(519*z+73) < 2^t := by omega
  have hEq : 346*u+54+4*(519*z+73)=346*2^t := by
    dsimp [t]
    omega
  exact subtract_small_power_divisor t n 346
    (346*u+54) (519*z+73) (by omega) hsmall hEq hdiv

/-- Complete 2-adic equivalence on the authentic low-stop ray.
    The gargantuan Q=346u+54 has EXACTLY the same low dyadic divisibility
    as 4*(519z+73): for every exponent n, no size cutoff. -/
theorem low_mass_divisor_iff (z u n : Nat)
    (hu : u+6*z+1=2^(1024*z+129)) :
    (2^(n+2) ∣ 346*u+54) ↔ (2^n ∣ 519*z+73) := by
  let t := 1024*z+129
  let s := 1024*z+127
  have hlin : s+1 ≤ 2^s := linear_le_power s
  have hC : 519*z+73 < 2^s := by
    dsimp [s] at *
    omega
  have ht : t=s+2 := by dsimp [t,s]
  have htpow : 2^t=4*2^s := by
    rw [ht,Nat.pow_add]
    omega
  have hsmall : 4*(519*z+73) < 2^t := by omega
  have hEq : 346*u+54+4*(519*z+73)=346*2^t := by
    dsimp [t]
    omega
  exact subtract_small_power_divisor_iff t n 346
    (346*u+54) (519*z+73) (by omega) hsmall hEq

/-- Every exact original-section low-stop incoming bounce is bound by
    the logarithm of its INDEX z, NOT by the unbounded giant exponent
    of its target. The full source-parent classification supplies n even
    and the raw source equations; divisibility forces 2^n|(519z+73). -/
theorem all_low_ray_parent_depth_logbound
    (z u a k : Nat)
    (hu : u+6*z+1=2^(1024*z+129))
    (hedge : secNext (a,k)=some (180*u+28,166*u+25)) :
    ∃ n : Nat,
      n%2=0 ∧ n≤Nat.log2 (519*z+73) ∧
      3≤a ∧ a<2*k ∧
      346*u+54=2^n*(2*(a-1)+8) ∧
      2*k+a+7+3*n=512*u+78 := by
  obtain ⟨n,hn,ha,hlow,hpow,hcost⟩ :=
    BB6.Agent13LowFanPower.all_low_ray_parents_are_even_bounce
      z u a k hu hedge
  have hao : a%2=1 := by omega
  have hval : a-1=2*((a-1)/2) := by omega
  have hbase : 2*(a-1)+8=4*((a-1)/2+2) := by omega
  have hpowexp : 2^(n+2)=4*2^n := by
    rw [show n+2=2+n by omega,Nat.pow_add]
  have hdiv : 2^(n+2)∣346*u+54 := by
    refine ⟨(a-1)/2+2,?_⟩
    rw [hpowexp]
    calc
      346*u+54=2^n*(2*(a-1)+8) := hpow
      _=2^n*(4*((a-1)/2+2)) := by rw [hbase]
      _=(4*2^n)*((a-1)/2+2) := by ac_rfl
  have hzdiv : 2^n∣519*z+73 := low_mass_divisor z u n hu hdiv
  have hbound : 2^n≤519*z+73 := Nat.le_of_dvd (by omega) hzdiv
  have hlog : n≤Nat.log2 (519*z+73) :=
    (Nat.le_log2 (by omega)).mpr hbound
  have hcost' : 2*k+a+7+3*n=512*u+78 := by omega
  exact ⟨n,hn,hlog,ha,hlow,hpow,hcost'⟩

#print axioms subtract_small_power_divisor
#print axioms subtract_small_power_divisor_iff
#print axioms low_mass_divisor
#print axioms low_mass_divisor_iff
#print axioms all_low_ray_parent_depth_logbound
end BB6.Agent13LowFanDivisor
