import RayDepthResidue

set_option maxHeartbeats 0

namespace CascadeRayTwoTierDepth
open CascadeRayDepthResidue CascadeRayDepthHensel CascadeRayPeriod

/-- The second-tier predecessor-state numerator, as opposed to the
    odd-band numerator. -/
def twoTierDepthNumerator (n j : Nat) : Int :=
  16*signedZ n j - 9*(12*(2:Int)^n+6*n+3)

/-- The unique depth residue at each ternary precision for which the
    second-tier predecessor-state numerator vanishes. -/
def twoTierDepthResidue (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let b := twoTierDepthResidue n k
      let a : Int :=
        16*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := twoTierDepthNumerator n b/(3:Int)^(k+1)
      b + henselDigit q a * depthPeriod k

private theorem twoTier_mod_three_even_iff (n j : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    (3:Int)∣twoTierDepthNumerator n j ↔ j%2=0 := by
  have hmod : twoTierDepthNumerator n j%3 = signedZ n j%3 := by
    dsimp [twoTierDepthNumerator]
    simp [Int.sub_emod,Int.mul_emod]
  rw [Int.dvd_iff_emod_eq_zero,hmod,Int.dvd_iff_emod_eq_zero]
  exact signedZ_mod_three_even_iff n j hn

private theorem twoTierDepthCoeff_unit (n b k : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    (16*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)%3≠0 := by
  have h := rayCoeff_unit n b k hn
  have h16 : (16:Int)%3=1 := by decide
  rw [Int.mul_emod]
  simpa [h16] using h

private theorem twoTierDepth_lift_criterion (n b k t : Nat)
    (ht : t<3)
    (hbase : (3:Int)^(k+1)∣twoTierDepthNumerator n b) :
    (3:Int)^(k+2)∣twoTierDepthNumerator n (b+t*depthPeriod k) ↔
      (3:Int)∣(twoTierDepthNumerator n b/(3:Int)^(k+1)-
        (16*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)*t) := by
  let c : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  let a : Int := 16*c
  let m : Int := (3:Int)^(k+1)
  have hmne : m≠0 := by
    change (3:Int)^(k+1)≠0
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM : (3:Int)^(k+2)=(3:Int)*m := by
    dsimp [m]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hs := signedZ_shift_digit_mod n b k t ht
  have hs' :
      signedZ n (b+t*depthPeriod k)%(3:Int)^(k+2)=
        (signedZ n b-m*(c*t))%(3:Int)^(k+2) := by
    simpa [m,c,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] using hs
  have hsdvd :
      (3:Int)^(k+2)∣
        signedZ n (b+t*depthPeriod k)-(signedZ n b-m*(c*t)) := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 hs'
  have hTdiff :
      twoTierDepthNumerator n (b+t*depthPeriod k)-
        (twoTierDepthNumerator n b-m*(a*t)) =
          16*(signedZ n (b+t*depthPeriod k)-
            (signedZ n b-m*(c*t))) := by
    dsimp [twoTierDepthNumerator,a,c]
    rw [Int.mul_sub,Int.mul_sub]
    have hprod : 16*(m*(c*t))=m*(16*c*t) := by ac_rfl
    rw [hprod]
    omega
  have hTdiv :
      (3:Int)^(k+2)∣
        twoTierDepthNumerator n (b+t*depthPeriod k)-
          (twoTierDepthNumerator n b-m*(a*t)) := by
    rcases hsdvd with ⟨z,hz⟩
    refine ⟨16*z,?_⟩
    rw [hTdiff,hz]
    ac_rfl
  have hdiviff :
      (3:Int)^(k+2)∣twoTierDepthNumerator n (b+t*depthPeriod k) ↔
        (3:Int)^(k+2)∣twoTierDepthNumerator n b-m*(a*t) := by
    constructor
    · intro h
      exact dvd_sub h hTdiv
    · intro h
      exact dvd_add h hTdiv
  have hquot : m*(twoTierDepthNumerator n b/m)=twoTierDepthNumerator n b :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor :
      twoTierDepthNumerator n b-m*(a*t)=
        m*(twoTierDepthNumerator n b/m-a*t) := by
    calc
      _ = m*(twoTierDepthNumerator n b/m)-m*(a*t) := by rw [hquot]
      _ = m*(twoTierDepthNumerator n b/m-a*t) := by rw [Int.mul_sub]
  have hcomm : (3:Int)*m=m*3 := Int.mul_comm _ _
  rw [hdiviff,hfactor,hM,hcomm]
  exact Int.mul_dvd_mul_iff_left hmne

theorem twoTierDepthResidue_lt (n k : Nat) :
    twoTierDepthResidue n k < depthPeriod k := by
  induction k with
  | zero =>
      simp [twoTierDepthResidue,depthPeriod]
  | succ k ih =>
      let b := twoTierDepthResidue n k
      let a : Int :=
        16*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := twoTierDepthNumerator n b/(3:Int)^(k+1)
      let d := henselDigit q a
      have hd : d<3 := henselDigit_lt q a
      have hmul := Nat.mul_le_mul_right (depthPeriod k)
        (show d≤2 by omega)
      have hnext := depthPeriod_next k
      have hdef : twoTierDepthResidue n (k+1)=b+d*depthPeriod k := rfl
      rw [hdef,hnext]
      omega

private theorem twoTierDepthResidue_good (n k : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    (3:Int)^(k+1)∣twoTierDepthNumerator n (twoTierDepthResidue n k) := by
  induction k with
  | zero =>
      have h := (twoTier_mod_three_even_iff n 0 hn).mpr (by decide)
      simpa [twoTierDepthResidue] using h
  | succ k ih =>
      let b := twoTierDepthResidue n k
      let c : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let a : Int := 16*c
      let q : Int := twoTierDepthNumerator n b/(3:Int)^(k+1)
      let d := henselDigit q a
      have ha : a%3≠0 := by
        simpa [a,c] using twoTierDepthCoeff_unit n b k hn
      have hd : d<3 := henselDigit_lt q a
      have hdiv : (3:Int)∣q-a*d := by
        simpa [d] using henselDigit_divides q a ha
      have hbase : (3:Int)^(k+1)∣twoTierDepthNumerator n b := ih
      have hlift := (twoTierDepth_lift_criterion n b k d hd hbase).mpr
        (by simpa [q,a,c] using hdiv)
      simpa [twoTierDepthResidue,b,a,c,q,d] using hlift

private theorem twoTier_period_dvd_iff (n j k m : Nat) :
    ((3:Int)^(k+1)∣twoTierDepthNumerator n (j+m*depthPeriod k)) ↔
    ((3:Int)^(k+1)∣twoTierDepthNumerator n j) := by
  have hs := signedZ_period_mul n j k m
  have hsdvd :
      (3:Int)^(k+1)∣
        signedZ n (j+m*depthPeriod k)-signedZ n j := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 hs
  have hTdiff :
      twoTierDepthNumerator n (j+m*depthPeriod k)-
        twoTierDepthNumerator n j =
          16*(signedZ n (j+m*depthPeriod k)-signedZ n j) := by
    dsimp [twoTierDepthNumerator]
    omega
  have hTdiv :
      (3:Int)^(k+1)∣
        twoTierDepthNumerator n (j+m*depthPeriod k)-
          twoTierDepthNumerator n j := by
    rcases hsdvd with ⟨z,hz⟩
    refine ⟨16*z,?_⟩
    rw [hTdiff,hz]
    ac_rfl
  constructor
  · intro h
    exact dvd_sub h hTdiv
  · intro h
    exact dvd_add h hTdiv

private theorem twoTier_period_dvd_iff (n j k m : Nat) :
    ((3:Int)^(k+1)∣twoTierDepthNumerator n (j+m*depthPeriod k)) ↔
    ((3:Int)^(k+1)∣twoTierDepthNumerator n j) := by
  simp only [Int.dvd_iff_emod_eq_zero, twoTierDepthNumerator,
    Int.sub_emod, Int.mul_emod]
  rw [signedZ_period_mul]

private theorem twoTier_period_mod_dvd_iff (n j k : Nat) :
    ((3:Int)^(k+1)∣twoTierDepthNumerator n j) ↔
    ((3:Int)^(k+1)∣twoTierDepthNumerator n (j%depthPeriod k)) := by
  have h := twoTier_period_dvd_iff n (j%depthPeriod k) k
    (j/depthPeriod k)
  have he : j%depthPeriod k+(j/depthPeriod k)*depthPeriod k=j :=
    Nat.mod_add_div' j (depthPeriod k)
  rw [he] at h
  exact h

private theorem twoTier_small_digit_unique (n k : Nat)
    (hn : n%6=4 ∨ n%6=5) (t : Nat) (ht : t<3) :
    ((3:Int)^(k+2)∣twoTierDepthNumerator n
      (twoTierDepthResidue n k+t*depthPeriod k)) ↔
    t=henselDigit
      (twoTierDepthNumerator n (twoTierDepthResidue n k)/(3:Int)^(k+1))
      (16*(2*n+3:Int)*(2:Int)^(twoTierDepthResidue n k+1)*depthCoeff k) := by
  let b := twoTierDepthResidue n k
  let c : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  let a : Int := 16*c
  let q : Int := twoTierDepthNumerator n b/(3:Int)^(k+1)
  have ha : a%3≠0 := by
    simpa [a,c] using twoTierDepthCoeff_unit n b k hn
  have hbase := twoTierDepthResidue_good n k hn
  have hc := twoTierDepth_lift_criterion n b k t ht hbase
  constructor
  · intro hh
    have hd : (3:Int)∣q-a*t := hc.mp hh
    exact henselDigit_div q a ha t ht hd
  · intro ht'
    subst t
    apply hc.mpr
    exact henselDigit_divides q a ha

/-- At every ternary precision, the second-tier predecessor-state
    numerator has exactly one depth residue class. -/
theorem twoTierDepthResidue_iff (n k j : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    ((3:Int)^(k+1)∣twoTierDepthNumerator n j) ↔
      j%depthPeriod k=twoTierDepthResidue n k := by
  induction k generalizing j with
  | zero =>
      have h := twoTier_mod_three_even_iff n j hn
      simpa [depthPeriod,twoTierDepthResidue] using h
  | succ k ih =>
      let p := depthPeriod k
      let pn := depthPeriod (k+1)
      let b := twoTierDepthResidue n k
      let d := henselDigit
        (twoTierDepthNumerator n b/(3:Int)^(k+1))
        (16*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)
      have hstep : pn=3*p := depthPeriod_next k
      have hdiv : (3:Int)^(k+1)∣(3:Int)^(k+2) := by
        refine ⟨3,?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz : (3:Int)^(k+2)∣twoTierDepthNumerator n (j%pn) :=
          (twoTier_period_mod_dvd_iff n j (k+1)).mp hx
        have hlo : (3:Int)^(k+1)∣twoTierDepthNumerator n (j%pn) := by
          cases hz with
          | intro w hw =>
            cases hdiv with
            | intro v hv =>
              refine ⟨v*w,?_⟩
              rw [hw,hv]
              ac_rfl
        have hb : (j%pn)%p=b := (ih (j%pn)).mp hlo
        have hp : 0<p := depthPeriod_pos k
        have hjlt : j%pn<3*p := by
          have h := Nat.mod_lt j (depthPeriod_pos (k+1))
          simpa only [pn,hstep] using h
        have ht : (j%pn)/p<3 := by
          apply (Nat.div_lt_iff_lt_mul hp).mpr
          exact hjlt
        have heq : j%pn=b+((j%pn)/p)*p := by
          have hh := Nat.mod_add_div' (j%pn) p
          omega
        have hd' := (twoTier_small_digit_unique n k hn ((j%pn)/p) ht).mp
          (by rw [←heq]; exact hz)
        have hnext : twoTierDepthResidue n (k+1)=b+d*p := rfl
        have hdnum : (j%pn)/p=d := by simpa only [b,d] using hd'
        have htarget : j%pn=b+d*p := by rw [←hdnum]; exact heq
        change j%pn=twoTierDepthResidue n (k+1)
        rw [hnext]
        exact htarget
      · intro hx
        apply (twoTier_period_mod_dvd_iff n j (k+1)).mpr
        rw [hx]
        exact twoTierDepthResidue_good n (k+1) hn

/-- Exactly one residue is divisible at each precision inside a full
    depth period for the second-tier numerator. -/
theorem twoTierDepthResidue_unique_in_period (n k j : Nat)
    (hn : n%6=4 ∨ n%6=5) (hj : j<depthPeriod k) :
    ((3:Int)^(k+1)∣twoTierDepthNumerator n j) ↔
      j=twoTierDepthResidue n k := by
  rw [twoTierDepthResidue_iff n k j hn]
  simp only [Nat.mod_eq_of_lt hj]

#print axioms twoTierDepthResidue_unique_in_period
#print axioms twoTierDepthResidue_iff
#print axioms twoTierDepthResidue_good
end CascadeRayTwoTierDepth
