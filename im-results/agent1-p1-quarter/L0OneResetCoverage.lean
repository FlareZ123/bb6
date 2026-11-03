import L0OneResetBridge

namespace BB6.Agent1OneReset
open BB6.Agent1RootWall
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent45TwoRoot

/-- L0 has no nontrivial all-upper inverse prefix that can enter another
    authentic odd sector (b divisible by four). This uses the exact
    2-adic valuation two of the L0 root's b+12. -/
theorem l0_upper_prefix_has_zero_length
    (q bp dp mp r : Nat) (hq : 1≤q)
    (hpre : UpperTail
      (4*u2 q-4) (4*u2 q+9) 0 bp dp mp r)
    (hmod : bp%4=0) : r=0 := by
  let u := u2 q
  let P := 2^(16*q)
  have hquad : 65536*q*q≤P := large_power q hq
  have hqq : q≤q*q := by
    have h:=Nat.mul_le_mul_right q hq
    omega
  have hquad' : 65536*(q*q)≤P := by
    calc
      65536*(q*q)=65536*q*q := by ac_rfl
      _≤P := hquad
  have hqbig : 65536*q≤P := by
    have h:=Nat.mul_le_mul_left 65536 hqq
    omega
  have hu : u+4*q+3=7*P := by dsimp [u,u2,P]; omega
  have hu1 : 1≤u := by omega
  have hp2 : P%2=0 := by
    have hpow : 2^1 ∣ 2^(16*q) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hh : 2 ∣ P := by simpa [P] using hpow
    exact Nat.dvd_iff_mod_eq_zero.mp hh
  have huodd : u%2=1 := by omega
  have hrootmod : ((4*u-4)+12)%8=4 := by omega
  have hdy := upper_tail_dyadic (4*u2 q-4) (4*u2 q+9)
    0 bp dp mp r hpre
  by_cases hr:r=0
  · exact hr
  have hrpos : 1≤r := by omega
  have hpdiv2 : 2∣2^r := by
    simpa using Nat.pow_dvd_pow 2 (by omega : 1≤r)
  have hbdiv4 : 4∣bp+12 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  obtain ⟨a,ha⟩:=hpdiv2
  obtain ⟨z,hz⟩:=hbdiv4
  have hdiv8 : 8∣2^r*(bp+12) := by
    refine ⟨a*z,?_⟩
    rw [ha,hz]
    calc
      (2*a)*(4*z)=(2*4)*(a*z) := by ac_rfl
      _=8*(a*z) := by omega
  have hdivroot : 8 ∣ (4*u-4)+12 := by
    have hshift : 4*u2 q-4=4*u-4 := rfl
    rw [←hshift,←hdy.1]
    exact hdiv8
  have hrootzero := Nat.dvd_iff_mod_eq_zero.mp hdivroot
  omega

theorem l0_upper_prefix_trivial
    (q bp dp mp r : Nat) (hq : 1≤q)
    (hpre : UpperTail
      (4*u2 q-4) (4*u2 q+9) 0 bp dp mp r)
    (hmod : bp%4=0) :
    bp=4*u2 q-4 ∧ dp=4*u2 q+9 ∧ mp=0 := by
  have hr := l0_upper_prefix_has_zero_length q bp dp mp r hq hpre hmod
  cases hpre with
  | root =>
    exact ⟨rfl,rfl,rfl⟩
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    omega

/-- Every exactly-one-reset authentic L0 inverse path, with any
    number of upper branches before and after its positive-depth reset,
    misses the affine wall for all q>=1. -/
theorem l0_one_reset_cone_no_wall
    (q bp dp mp r t k c b d m n : Nat)
    (hq : 1≤q)
    (hpre : UpperTail (4*u2 q-4) (4*u2 q+9) 0 bp dp mp r)
    (hbp : 8≤bp) (hb4 : bp%4=0) (hdp : dp%2=1)
    (hi : inverseAt bp dp t=some (k,c))
    (ht : 1≤t) (hk : 2≤k) (hc : c%2=1)
    (hpost : UpperTail (2*k-4) (c+4) (mp+t+1) b d m n)
    (hwall : b=4*m+64*q+12) : False := by
  obtain ⟨hB,hD,hM⟩ :=
    l0_upper_prefix_trivial q bp dp mp r hq hpre hb4
  subst bp
  subst dp
  subst mp
  exact l0_first_reset_no_wall q t k c b d m n hq ht hk hc
    hi (by simpa using hpost) hwall

#print axioms l0_upper_prefix_has_zero_length
#print axioms l0_one_reset_cone_no_wall
end BB6.Agent1OneReset
