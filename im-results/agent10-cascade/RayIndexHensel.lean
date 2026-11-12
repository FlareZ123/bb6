import RayDepthResidue
set_option maxHeartbeats 0

/-!
The signed #746 inverse-ray numerator has a second, complementary Hensel
direction.  RayDepthResidue lifts the depth coordinate for fixed fatal n;
this file lifts the fatal-sector index for fixed even depth.

For every even j and s in {4,5}, exactly one h modulo 3^k makes
3^(k+1) divide signedZ (s+6*h) j.  The two residue maps are inverse
coordinates on the same 3-adic congruence surface.
-/

namespace CascadeRayIndexHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

/-- One step of the fatal-sector index is six in the original n-coordinate. -/
def indexSector (s h : Nat) : Nat := s+6*h

/-- The unique ternary index residue at a fixed even ray depth. -/
def indexResidue (s j : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let b := indexResidue s j k
      let a : Int := 4*((2:Int)^(j+1)-1)
      let q : Int := signedZ (indexSector s b) j/(3:Int)^(k+1)
      b + henselDigit q a * 3^k

/-- One exact even-depth index shift.  The exponential term changes only
    at precision k+2; the linear term supplies a unit ternary digit. -/
private theorem signedZ_index_step (n j k : Nat) :
    signedZ (n+depthPeriod (k+1)) j =
      signedZ n j
        - (3:Int)^(k+1)*(4*((2:Int)^(j+1)-1))
        + (3:Int)^(k+2)*(8*(2:Int)^n*depthCoeff (k+1)) := by
  have hpowNat : (2:Nat)^(n+depthPeriod (k+1)) =
      (2:Nat)^n*(1+3^(k+2)*depthCoeff (k+1)) := by
    calc
      (2:Nat)^(n+depthPeriod (k+1)) =
          (2:Nat)^n*(2:Nat)^(depthPeriod (k+1)) := by
            rw [Nat.pow_add]
      _ = (2:Nat)^n*(1+3^(k+2)*depthCoeff (k+1)) := by
            rw [pow_depth_period]
  have hpowInt : (2:Int)^(n+depthPeriod (k+1)) =
      (2:Int)^n*(1+(3:Int)^(k+2)*depthCoeff (k+1)) := by
    exact_mod_cast hpowNat
  have hlin : (2:Int)*(n+depthPeriod (k+1))+3 =
      (2:Int)*n+3+4*(3:Int)^(k+1) := by
    simp [depthPeriod,Nat.pow_succ]
    omega
  dsimp [signedZ]
  push_cast
  rw [hpowInt,hlin]
  simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
  omega

private theorem signedZ_index_step_divisible (n j k : Nat) :
    (3:Int)^(k+1) ∣
      signedZ (n+depthPeriod (k+1)) j-signedZ n j := by
  have hstep:=signedZ_index_step n j k
  have hpow : (3:Int)^(k+2)=3*(3:Int)^(k+1) := by
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
  let P : Int := (3:Int)^(k+1)
  let a : Int := 4*((2:Int)^(j+1)-1)
  let c : Int := 8*(2:Int)^n*depthCoeff (k+1)
  have hfactor : P*(-a+3*c) = -P*a+(3*P)*c := by
    simp [Int.mul_add,Int.mul_neg,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
  refine ⟨-a+3*c,?_⟩
  calc
    signedZ (n+depthPeriod (k+1)) j-signedZ n j =
        -P*a+(3:Int)^(k+2)*c := by
          rw [hstep]
          dsimp [P,a,c]
          omega
    _ = P*(-a+3*c) := by
          rw [hpow]
          exact hfactor.symm

private theorem signedZ_index_step_mod (n j k : Nat) :
    signedZ (n+depthPeriod (k+1)) j%(3:Int)^(k+1) =
      signedZ n j%(3:Int)^(k+1) := by
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  exact Int.dvd_iff_emod_eq_zero.mp (signedZ_index_step_divisible n j k)

/-- Every full index stride preserves divisibility at the current precision. -/
private theorem signedZ_index_period (n j k m : Nat) :
    signedZ (n+m*depthPeriod (k+1)) j%(3:Int)^(k+1) =
      signedZ n j%(3:Int)^(k+1) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hidx : n+(m+1)*depthPeriod (k+1) =
          (n+m*depthPeriod (k+1))+depthPeriod (k+1) := by
        rw [Nat.succ_mul]
        omega
      rw [hidx,signedZ_index_step_mod,ih]

/-- The three possible next index digits act linearly modulo 3^(k+2). -/
theorem signedZ_index_shift_digit_mod (n j k t : Nat)
    (ht:t<3) :
    signedZ (n+t*depthPeriod (k+1)) j%(3:Int)^(k+2) =
      (signedZ n j-(3:Int)^(k+1)*
        (4*((2:Int)^(j+1)-1)*t))%(3:Int)^(k+2) := by
  have hpowNat : (2:Nat)^(n+t*depthPeriod (k+1)) =
      (2:Nat)^n*(1+t*3^(k+2)*depthCoeff (k+1)+
        3^(k+3)*depthError (k+1) t) := by
    calc
      (2:Nat)^(n+t*depthPeriod (k+1)) =
          (2:Nat)^n*(2:Nat)^(t*depthPeriod (k+1)) := by
            rw [Nat.pow_add]
      _ = (2:Nat)^n*(1+t*3^(k+2)*depthCoeff (k+1)+
          3^(k+3)*depthError (k+1) t) := by
            rw [pow_period_digit (k+1) t ht]
  have hpowInt : (2:Int)^(n+t*depthPeriod (k+1)) =
      (2:Int)^n*(1+t*(3:Int)^(k+2)*depthCoeff (k+1)+
        (3:Int)^(k+3)*depthError (k+1) t) := by
    exact_mod_cast hpowNat
  have hlin : (2:Int)*(n+t*depthPeriod (k+1))+3 =
      (2:Int)*n+3+4*(3:Int)^(k+1)*t := by
    simp [depthPeriod,Nat.pow_succ]
    omega
  have hz : signedZ (n+t*depthPeriod (k+1)) j =
      signedZ n j-(3:Int)^(k+1)*
        (4*((2:Int)^(j+1)-1)*t)
        +(3:Int)^(k+2)*
          (8*(2:Int)^n*(t*depthCoeff (k+1)+
            3*depthError (k+1) t)) := by
    dsimp [signedZ]
    push_cast
    rw [hpowInt,hlin]
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    omega
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  apply Int.emod_eq_zero_of_dvd
  refine ⟨8*(2:Int)^n*(t*depthCoeff (k+1)+
    3*depthError (k+1) t),?_⟩
  rw [hz]
  omega

/-- Divisibility at the next precision is equivalent to the unique
    ternary quotient digit selected by the index shift. -/
private theorem signedZ_index_lift_criterion (n j k t : Nat) (ht:t<3)
    (hbase : (3:Int)^(k+1) ∣ signedZ n j) :
    (3:Int)^(k+2) ∣ signedZ (n+t*depthPeriod (k+1)) j ↔
      (3:Int) ∣
        (signedZ n j/(3:Int)^(k+1)-
          (4*((2:Int)^(j+1)-1))*t) := by
  let m : Int := (3:Int)^(k+1)
  let a : Int := 4*((2:Int)^(j+1)-1)
  have hmne:m≠0:=by
    change (3:Int)^(k+1)≠0
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM:(3:Int)^(k+2)=(3:Int)*m:=by
    dsimp [m]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hmod:=signedZ_index_shift_digit_mod n j k t ht
  have hmod' : signedZ (n+t*depthPeriod (k+1)) j%(3:Int)^(k+2)=
      (signedZ n j-m*(a*t))%(3:Int)^(k+2) := by
    simpa [m,a,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using hmod
  have hdiviff : (3:Int)^(k+2)∣signedZ (n+t*depthPeriod (k+1)) j ↔
      (3:Int)^(k+2)∣(signedZ n j-m*(a*t)) := by
    rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero,hmod']
  have hquot : m*(signedZ n j/m)=signedZ n j :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor : signedZ n j-m*(a*t)=
      m*(signedZ n j/m-a*t) := by
    calc
      _ = m*(signedZ n j/m)-m*(a*t) := by
        exact congrArg (fun x:Int => x-m*(a*t)) hquot.symm
      _ = m*(signedZ n j/m-a*t) := by
        rw [Int.mul_sub]
  have hcomm:(3:Int)*m=m*3:=Int.mul_comm _ _
  rw [hdiviff,hfactor,hM,hcomm]
  exact Int.mul_dvd_mul_iff_left hmne

private theorem pow_two_mod_three (m : Nat) :
    2^m%3 = if m%2=0 then 1 else 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ,Nat.mul_mod,ih]
      by_cases hm:m%2=0
      · have hs:(m+1)%2=1:=by omega
        rw [if_pos hm]
        simp [hs]
      · have hm1:m%2=1:=by omega
        have hs:(m+1)%2=0:=by omega
        rw [if_neg hm]
        simp [hm1,hs]

/-- The index-lift coefficient is a unit, and in fact equals one modulo
    three, at every even ray depth. -/
theorem indexCoeff_mod_three (j:Nat) (hj:j%2=0) :
    (4*((2:Int)^(j+1)-1))%3=1 := by
  have hpNat:(2:Nat)^(j+1)%3=2 := by
    rw [pow_two_mod_three]
    have hodd:(j+1)%2=1:=by omega
    simp [hodd]
  have hpInt:((2:Int)^(j+1))%3=2:=by exact_mod_cast hpNat
  have hsub:(((2:Int)^(j+1)-1)%3)=1 := by
    rw [Int.sub_emod,hpInt]
    decide
  rw [Int.mul_emod]
  have hfour:(4:Int)%3=1:=by decide
  rw [hfour,hsub]
  decide

/-- The recursive lift has the expected canonical interval. -/
theorem indexResidue_lt (s j k:Nat) :
    indexResidue s j k<3^k := by
  induction k with
  | zero =>
      simp [indexResidue]
  | succ k ih =>
      let b:=indexResidue s j k
      let a:Int:=4*((2:Int)^(j+1)-1)
      let q:Int:=signedZ (indexSector s b) j/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hd: d<3:=henselDigit_lt q a
      have hle:d≤2:=by omega
      have hmul:=Nat.mul_le_mul_right (3^k) hle
      have hpow:3^(k+1)=3*3^k:=by
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      change b+d*3^k<3^(k+1)
      omega

/-- At every precision, the recursive residue is an actual solution. -/
private theorem indexResidue_good (s j k:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    indexResidue s j k<3^k ∧
      (3:Int)^(k+1)∣signedZ (indexSector s (indexResidue s j k)) j := by
  induction k with
  | zero =>
      constructor
      · simp [indexResidue]
      · have hsector:(s+6*0)%6=4∨(s+6*0)%6=5:=by
          rcases hs with hs4|hs5
          · rw [hs4]; simp
          · rw [hs5]; simp
        have hmod: signedZ s j%3=0 :=
          (signedZ_mod_three_even_iff s j hsector).mpr hj
        have hdiv:(3:Int)∣signedZ s j :=
          Int.dvd_iff_emod_eq_zero.mpr hmod
        simpa [indexResidue,indexSector] using hdiv
  | succ k ih =>
      let b:=indexResidue s j k
      let a:Int:=4*((2:Int)^(j+1)-1)
      let q:Int:=signedZ (indexSector s b) j/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hb:b<3^k:=ih.1
      have hbase:(3:Int)^(k+1)∣signedZ (indexSector s b) j:=ih.2
      have ha:a%3≠0:=by
        simpa [a] using indexCoeff_mod_three j hj
      have hd:d<3:=henselDigit_lt q a
      have hdiv:(3:Int)∣q-a*d:=by
        simpa [d] using henselDigit_divides q a ha
      have hlift: (3:Int)^(k+2)∣
          signedZ (indexSector s b+d*depthPeriod (k+1)) j :=
        (signedZ_index_lift_criterion (indexSector s b) j k d hd hbase).mpr
          (by simpa [q,a] using hdiv)
      have hshift:indexSector s (b+d*3^k)=
          indexSector s b+d*depthPeriod (k+1):=by
        simp [indexSector,depthPeriod,Nat.pow_succ]
        omega
      have hbound:b+d*3^k<3^(k+1):=by
        have hdle:d≤2:=by omega
        have hmul:=Nat.mul_le_mul_right (3^k) hdle
        have hpow:3^(k+1)=3*3^k:=by rw [Nat.pow_succ]
        omega
      constructor
      · exact hbound
      · rw [hshift]
        exact hlift

private theorem index_period_dvd_iff (s j k h m:Nat) :
    (3:Int)^(k+1)∣signedZ (indexSector s (h+m*3^k)) j ↔
      (3:Int)^(k+1)∣signedZ (indexSector s h) j := by
  have hshift:indexSector s (h+m*3^k)=
      indexSector s h+m*depthPeriod (k+1):=by
    simp [indexSector,depthPeriod,Nat.pow_succ]
    omega
  rw [hshift,Int.dvd_iff_emod_eq_zero]
  exact signedZ_index_period (indexSector s h) j k m

private theorem index_period_mod_dvd_iff (s j k h:Nat) :
    (3:Int)^(k+1)∣signedZ (indexSector s h) j ↔
      (3:Int)^(k+1)∣signedZ (indexSector s (h%3^k)) j := by
  have hper:=index_period_dvd_iff s j k (h%3^k) (h/3^k)
  have heq:h%3^k+(h/3^k)*3^k=h:=Nat.mod_add_div' h (3^k)
  rw [heq] at hper
  exact hper

/-- Exact index-coordinate Hensel theorem: in every complete 3^k block
    there is precisely one fatal-sector index whose ray numerator has
    3-adic valuation at least k+1. -/
theorem indexResidue_iff (s j k h:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    (3:Int)^(k+1)∣signedZ (indexSector s h) j ↔
      h%3^k=indexResidue s j k := by
  induction k generalizing h with
  | zero =>
      have hsector:(indexSector s h)%6=4∨(indexSector s h)%6=5:=by
        rcases hs with hs4|hs5
        · rw [hs4]; simp [indexSector]
        · rw [hs5]; simp [indexSector]
      have hmod:(signedZ (indexSector s h) j)%3=0 :=
        (signedZ_mod_three_even_iff (indexSector s h) j hsector).mpr hj
      have hdiv:(3:Int)∣signedZ (indexSector s h) j :=
        Int.dvd_iff_emod_eq_zero.mpr hmod
      have hres:h%3^0=indexResidue s j 0:=by simp [indexResidue]
      constructor
      · intro _
        exact hres
      · intro _
        simpa [indexResidue] using hdiv
  | succ k ih =>
      let P:=3^k
      let pn:=3^(k+1)
      let b:=indexResidue s j k
      let a:Int:=4*((2:Int)^(j+1)-1)
      let q:Int:=signedZ (indexSector s b) j/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hstep:pn=3*P:=by
        dsimp [pn,P]
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      have hdiv:(3:Int)^(k+1)∣(3:Int)^(k+2):=by
        refine ⟨3,?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz:(3:Int)^(k+2)∣signedZ (indexSector s (h%pn)) j :=
          (index_period_mod_dvd_iff s j (k+1) h).mp hx
        have hlo:(3:Int)^(k+1)∣signedZ (indexSector s (h%pn)) j:=by
          rcases hz with ⟨w,hw⟩
          rcases hdiv with ⟨v,hv⟩
          refine ⟨v*w,?_⟩
          rw [hw,hv]
          ac_rfl
        have haidx:(h%pn)%P=b:=(ih (h%pn)).mp hlo
        have hp:0<P:=Nat.pow_pos (by decide)
        have hjlt:h%pn<3*P:=by
          have hh:=Nat.mod_lt h (Nat.pow_pos (by decide))
          simpa only [pn,hstep] using hh
        have ht:(h%pn)/P<3:=
          (Nat.div_lt_iff_lt_mul hp).mpr hjlt
        have hsplit:h%pn=(h%pn)%P+((h%pn)/P)*P:=
          Nat.mod_add_div' (h%pn) P
        have hshift:indexSector s (h%pn)=
            indexSector s b+((h%pn)/P)*depthPeriod (k+1):=by
          rw [hsplit,haidx]
          simp [indexSector,depthPeriod,Nat.pow_succ]
          omega
        have hbase:(3:Int)^(k+1)∣signedZ (indexSector s b) j:=
          (indexResidue_good s j k hs hj).2
        have hshiftdiv:(3:Int)^(k+2)∣
            signedZ (indexSector s b+((h%pn)/P)*depthPeriod (k+1)) j:=by
          rw [←hshift]
          exact hz
        have hcrit:(3:Int)∣q-a*((h%pn)/P):=
          (signedZ_index_lift_criterion (indexSector s b) j k
            ((h%pn)/P) ht hbase).mp hshiftdiv
        have haunit:a%3≠0:=by
          simpa [a] using indexCoeff_mod_three j hj
        have hdigit:((h%pn)/P)=d:=
          henselDigit_div q a haunit ((h%pn)/P) ht
            (by simpa [q,a] using hcrit)
        have htarget:h%pn=b+d*P:=by
          rw [hsplit,haidx,hdigit]
        have hnext:indexResidue s j (k+1)=b+d*P:=rfl
        have hcanon:h%pn=indexResidue s j (k+1):=by
          rw [hnext]
          exact htarget
        change h%3^(k+1)=indexResidue s j (k+1)
        simpa [pn] using hcanon
      · intro hx
        have hcanon:h%pn=indexResidue s j (k+1):=by
          simpa [pn] using hx
        apply (index_period_mod_dvd_iff s j (k+1) h).mpr
        rw [hcanon]
        exact (indexResidue_good s j (k+1) hs hj).2

/-- The index- and depth-direction lifts are mutual inverses on the
    same 3-adic zero set: a depth class is selected exactly when the
    fatal-sector index belongs to its corresponding index class. -/
theorem depth_index_duality (s h j k:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    j%depthPeriod k=depthResidue (indexSector s h) k ↔
      h%3^k=indexResidue s j k := by
  have hsector:(indexSector s h)%6=4∨(indexSector s h)%6=5:=by
    rcases hs with hs4|hs5
    · rw [hs4]; simp [indexSector]
    · rw [hs5]; simp [indexSector]
  have hdepth:=depthResidue_iff (indexSector s h) k j hsector
  have hindex:=indexResidue_iff s j k h hs hj
  exact hdepth.symm.trans hindex

/-- The depth selector is always an even depth, since its numerator
    is divisible by three at every positive precision. -/
private theorem depthResidue_even (n k:Nat)
    (hn:n%6=4∨n%6=5) :
    depthResidue n k%2=0 := by
  have hlt:=depthResidue_lt n k
  have hdiv:(3:Int)^(k+1)∣signedZ n (depthResidue n k):=
    (depthResidue_iff n k (depthResidue n k) hn).mpr
      (Nat.mod_eq_of_lt hlt)
  have h3pow:(3:Int)∣(3:Int)^(k+1):=by
    refine ⟨(3:Int)^k,?_⟩
    rw [Int.pow_succ]
    exact Int.mul_comm _ _
  have h3:(3:Int)∣signedZ n (depthResidue n k):=
    Int.dvd_trans h3pow hdiv
  have hmod:=Int.dvd_iff_emod_eq_zero.mp h3
  exact (signedZ_mod_three_even_iff n (depthResidue n k) hn).mp hmod

/-- Numerator for a second odd-parent step after an odd parent of
    the canonical ray node at depth j.  If 3^(t+1)d=Z_j(n), then
    nestedOddNumerator n j t / 3^(t+1) is exactly 2*x+5 for x=2^t*d. -/
def nestedOddNumerator (n j t:Nat) : Int :=
  (2:Int)^(t+1)*signedZ n j+5*(3:Int)^(t+1)

/-- The next odd-parent numerator has a unit-coefficient 3-adic index
    lift at every even ray depth. -/
private theorem nestedOddNumerator_shift_digit_mod (n j t k r:Nat)
    (hj:j%2=0) (hr:r<3) :
    nestedOddNumerator (n+r*depthPeriod (k+1)) j t%(3:Int)^(k+2) =
      (nestedOddNumerator n j t-
        (3:Int)^(k+1)*(2:Int)^(t+3)*
          ((2:Int)^(j+1)-1)*r)%(3:Int)^(k+2) := by
  let P : Int := (3:Int)^(k+1)
  let M : Int := (3:Int)^(k+2)
  have hz:=signedZ_index_shift_digit_mod n j k r hr
  have hdiv : M∣
      signedZ (n+r*depthPeriod (k+1)) j-
        (signedZ n j-P*(4*((2:Int)^(j+1)-1)*r)) := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).1
      (by simpa [P,M,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using hz)
  have hpow:(2:Int)^(t+3)=4*(2:Int)^(t+1):=by
    rw [show t+3=(t+1)+2 by omega,Int.pow_add]
    calc
      (2:Int)^(t+1)*2^2=(2:Int)^(t+1)*4:=by norm_num
      _=4*(2:Int)^(t+1):=Int.mul_comm _ _
  have hdiff :
      nestedOddNumerator (n+r*depthPeriod (k+1)) j t-
        (nestedOddNumerator n j t-
          P*(2:Int)^(t+3)*((2:Int)^(j+1)-1)*r) =
      (2:Int)^(t+1)*
        (signedZ (n+r*depthPeriod (k+1)) j-
          (signedZ n j-P*4*((2:Int)^(j+1)-1)*r)) := by
    dsimp [nestedOddNumerator]
    rw [hpow]
    simp [Int.mul_sub,Int.mul_add,Int.sub_add_assoc,Int.add_sub_assoc,
      Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] <;> omega
  have hdivW : M∣
      nestedOddNumerator (n+r*depthPeriod (k+1)) j t-
        (nestedOddNumerator n j t-
          P*(2:Int)^(t+3)*((2:Int)^(j+1)-1)*r) := by
    rcases hdiv with ⟨c,hc⟩
    refine ⟨(2:Int)^(t+1)*c,?_⟩
    rw [hdiff,hc]
    ac_rfl
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  exact Int.dvd_iff_emod_eq_zero.mp hdivW

/-- Exact next-digit criterion for the second odd-parent numerator. -/
private theorem nestedOddNumerator_lift_criterion (n j t k r:Nat)
    (hj:j%2=0) (hr:r<3)
    (hbase:(3:Int)^(k+1)∣nestedOddNumerator n j t) :
    (3:Int)^(k+2)∣nestedOddNumerator
        (n+r*depthPeriod (k+1)) j t ↔
      (3:Int)∣
        (nestedOddNumerator n j t/(3:Int)^(k+1)-
          (2:Int)^(t+3)*((2:Int)^(j+1)-1)*r) := by
  let P : Int := (3:Int)^(k+1)
  let M : Int := (3:Int)^(k+2)
  let a : Int := (2:Int)^(t+3)*((2:Int)^(j+1)-1)
  have hp:P≠0:=by
    dsimp [P]
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM:M=3*P:=by
    dsimp [M,P]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hmod:=nestedOddNumerator_shift_digit_mod n j t k r hj hr
  have hmod' :
      nestedOddNumerator (n+r*depthPeriod (k+1)) j t%M =
        (nestedOddNumerator n j t-P*(a*r))%M := by
    simpa [P,M,a,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using hmod
  have hdiviff : M∣nestedOddNumerator (n+r*depthPeriod (k+1)) j t ↔
      M∣(nestedOddNumerator n j t-P*(a*r)) := by
    rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero,hmod']
  have hquot : P*(nestedOddNumerator n j t/P)=nestedOddNumerator n j t :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor : nestedOddNumerator n j t-P*(a*r)=
      P*(nestedOddNumerator n j t/P-a*r) := by
    calc
      _ = P*(nestedOddNumerator n j t/P)-P*(a*r) := by
        rw [hquot]
      _ = P*(nestedOddNumerator n j t/P-a*r) := by
        rw [Int.mul_sub]
  rw [hdiviff,hfactor,hM]
  exact Int.mul_dvd_mul_iff_left hp

private theorem nestedOddCoeff_unit (j t:Nat) (hj:j%2=0) :
    ((2:Int)^(t+3)*((2:Int)^(j+1)-1))%3≠0 := by
  have hja:((2:Int)^(j+1)-1)%3=1:=by
    have h:=indexCoeff_mod_three j hj
    rw [Int.mul_emod] at h
    have hfour:(4:Int)%3=1:=by decide
    rw [hfour] at h
    simpa using h
  have hpNat:=pow_two_mod_three (t+3)
  have hpInt:((2:Int)^(t+3))%3=
      (if (t+3)%2=0 then (1:Int) else 2):=by
    exact_mod_cast hpNat
  rw [Int.mul_emod,hja,hpInt]
  by_cases ht:(t+3)%2=0 <;> simp [ht]

/-- Each nested odd-parent lift has exactly one of the three possible
    index digits. -/
theorem nestedOddNumerator_unique_lift (n j t k:Nat)
    (hj:j%2=0)
    (hbase:(3:Int)^(k+1)∣nestedOddNumerator n j t) :
    ∃! r, r<3 ∧
      (3:Int)^(k+2)∣nestedOddNumerator
        (n+r*depthPeriod (k+1)) j t := by
  let q:Int:=nestedOddNumerator n j t/(3:Int)^(k+1)
  let a:Int:=(2:Int)^(t+3)*((2:Int)^(j+1)-1)
  let d:=henselDigit q a
  have ha:a%3≠0:=by
    simpa [a] using nestedOddCoeff_unit j t hj
  have hd:d<3:=henselDigit_lt q a
  have hdiv:(3:Int)∣q-a*d:=by
    simpa [d] using henselDigit_divides q a ha
  have hgood:(3:Int)^(k+2)∣
      nestedOddNumerator (n+d*depthPeriod (k+1)) j t:=
    (nestedOddNumerator_lift_criterion n j t k d hj hd hbase).mpr
      (by simpa [q,a] using hdiv)
  refine ⟨d,⟨hd,hgood⟩,?_⟩
  intro r hr
  rcases hr with ⟨hrlt,hrdiv⟩
  have hcrit:(3:Int)∣q-a*r:=
    (nestedOddNumerator_lift_criterion n j t k r hj hrlt hbase).mp hrdiv
  exact henselDigit_div q a ha r hrlt (by simpa [q,a] using hcrit)

private theorem nestedOddNumerator_step_divisible (n j t k:Nat) :
    (3:Int)^(k+1)∣
      nestedOddNumerator (n+depthPeriod (k+1)) j t-
        nestedOddNumerator n j t := by
  have hz:=signedZ_index_step_divisible n j k
  rcases hz with ⟨c,hc⟩
  refine ⟨(2:Int)^(t+1)*c,?_⟩
  change
    (2:Int)^(t+1)*signedZ (n+depthPeriod (k+1)) j+
        5*(3:Int)^(t+1)-
      ((2:Int)^(t+1)*signedZ n j+5*(3:Int)^(t+1)) =
      (3:Int)^(k+1)*((2:Int)^(t+1)*c)
  calc
    _=(2:Int)^(t+1)*signedZ (n+depthPeriod (k+1)) j-
        (2:Int)^(t+1)*signedZ n j:=by omega
    _=(2:Int)^(t+1)*
        (signedZ (n+depthPeriod (k+1)) j-signedZ n j):=by
      rw [Int.mul_sub]
    _=(2:Int)^(t+1)*((3:Int)^(k+1)*c):=by rw [hc]
    _=(3:Int)^(k+1)*((2:Int)^(t+1)*c):=by ac_rfl

private theorem nestedOddNumerator_step_mod (n j t k:Nat) :
    nestedOddNumerator (n+depthPeriod (k+1)) j t%(3:Int)^(k+1) =
      nestedOddNumerator n j t%(3:Int)^(k+1) := by
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  exact Int.dvd_iff_emod_eq_zero.mp
    (nestedOddNumerator_step_divisible n j t k)

/-- Shifting the index by a full period preserves the numerator modulo
    the current Hensel precision. -/
private theorem nestedOddNumerator_period_mul (s j t h k m:Nat)
    (hj:j%2=0) :
    nestedOddNumerator (s+6*(h+m*3^k)) j t%(3:Int)^(k+1) =
      nestedOddNumerator (s+6*h) j t%(3:Int)^(k+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx :
          s+6*(h+(m+1)*3^k)=
            (s+6*(h+m*3^k))+depthPeriod (k+1) := by
        simp [depthPeriod,Nat.pow_succ,Nat.succ_mul]
        omega
      rw [hidx]
      exact (nestedOddNumerator_step_mod (s+6*(h+m*3^k)) j t k).trans ih

private theorem nestedOddNumerator_period_dvd_iff (s j t k h:Nat)
    (hj:j%2=0) :
    (3:Int)^(k+1)∣nestedOddNumerator (s+6*h) j t ↔
      (3:Int)^(k+1)∣nestedOddNumerator (s+6*(h%3^k)) j t := by
  rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero]
  have hperiod:=nestedOddNumerator_period_mul s j t (h%3^k) k (h/3^k) hj
  have he : h%3^k+(h/3^k)*3^k=h:=Nat.mod_add_div' h (3^k)
  rw [he] at hperiod
  constructor
  · intro hx
    rw [←hperiod]
    exact hx
  · intro hy
    rw [hperiod]
    exact hy

/-- At the t=3 high-q gate, the next index digit is exactly the
    quotient W_(j,3)(n)/3^8 modulo 3. -/
theorem tThreeHighGate_digit_eq_quotient_mod_three (n j:Nat)
    (hj:j%2=0) :
    (henselDigit
      (nestedOddNumerator n j 3/(3:Int)^8)
      ((2:Int)^6*((2:Int)^(j+1)-1)):Int) =
      (nestedOddNumerator n j 3/(3:Int)^8)%3 := by
  let q:Int:=nestedOddNumerator n j 3/(3:Int)^8
  let a:Int:=(2:Int)^6*((2:Int)^(j+1)-1)
  let d:=henselDigit q a
  have hja:((2:Int)^(j+1)-1)%3=1:=by
    have h:=indexCoeff_mod_three j hj
    rw [Int.mul_emod] at h
    have hfour:(4:Int)%3=1:=by decide
    rw [hfour] at h
    simpa using h
  have hpow:((2:Int)^6)%3=1:=by norm_num
  have ha:a%3=1:=by
    dsimp [a]
    rw [Int.mul_emod,hpow,hja]
    norm_num
  have hmod:=henselDigit_mod q a (by rw [ha]; norm_num)
  have hd:=henselDigit_lt q a
  have hcast:(d:Int)%3=(d:Int):=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hd)
  have hq:(d:Int)=q%3:=by
    have h:=hmod
    rw [Int.mul_emod,ha,hcast] at h
    have h' : (d:Int)%3=q%3:=by simpa using h
    rw [hcast] at h'
    exact h'
  simpa [q,d] using hq

/-- In the source equation for the second t=3 parent, its level index
    r satisfies r = 16*e - 2^(n-3) - n + 1.  The sector condition
    makes 2^(n-3)+n divisible by 3, hence r = e+1 mod 3. -/
theorem tThreeSecondParent_index_relation (n e r:Nat)
    (hn:20≤n) (hsector:n%6=4∨n%6=5)
    (hrrel:16*e=8*2^(n-6)+r+(n-6)+5) :
    r%3=(e+1)%3 := by
  have hpowNat : 8*2^(n-6)=2^(n-3) := by
    calc
      8*2^(n-6)=2^3*2^(n-6):=by norm_num
      _=2^((n-6)+3):=by
        rw [Nat.pow_add]
        exact Nat.mul_comm _ _
      _=2^(n-3):=by congr 1; omega
  have hrrel' : 16*e+1=2^(n-3)+r+n := by
    rw [hpowNat] at hrrel
    omega
  have hrrelI : (16:Int)*(e:Int)+1=(2:Int)^(n-3)+r+n := by
    exact_mod_cast hrrel'
  have hrformulaI : (r:Int)=16*e-(2:Int)^(n-3)-n+1 := by omega
  have hconst : (2^(n-3)+n)%3=0 := by
    have hpow:=pow_two_mod_three (n-3)
    rcases hsector with hs4|hs5
    · have hneq:(n-3)%2≠0:=by omega
      rw [if_neg hneq] at hpow
      omega
    · have hpar:(n-3)%2=0:=by omega
      rw [if_pos hpar] at hpow
      omega
  have hconstI : ((2:Int)^(n-3)+n)%3=0 := by exact_mod_cast hconst
  have hrmodI : (r:Int)%3=((e:Int)+1)%3 := by omega
  exact_mod_cast hrmodI

/-- The nested numerator starts in the zero class on both surviving
    fatal sectors, for every even ray depth and odd-parent exponent t. -/
theorem nestedOddNumerator_sector_mod_three (s h j t:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    nestedOddNumerator (s+6*h) j t%3=0 := by
  have hsector:(s+6*h)%6=4∨(s+6*h)%6=5:=by
    rcases hs with hs4|hs5
    · rw [hs4]; simp
    · rw [hs5]; simp
  have hZmod:signedZ (s+6*h) j%3=0:=
    (signedZ_mod_three_even_iff (s+6*h) j hsector).mpr hj
  have hZdiv:(3:Int)∣signedZ (s+6*h) j:=
    Int.dvd_iff_emod_eq_zero.mpr hZmod
  rcases hZdiv with ⟨z,hz⟩
  have hpow:(3:Int)^(t+1)=(3:Int)^t*3:=by
    rw [Int.pow_succ]
  apply Int.dvd_iff_emod_eq_zero.mp
  refine ⟨(2:Int)^(t+1)*z+5*(3:Int)^t,?_⟩
  dsimp [nestedOddNumerator]
  rw [hz,hpow]
  simp [Int.mul_add,Int.add_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] <;> omega

/-- Recursive index selector for the nested odd-parent numerator
    W_(j,t), fixing an even ray depth and selecting the fatal index. -/
def nestedOddIndexResidue (s j t:Nat) : Nat→Nat
  | 0 => 0
  | k+1 =>
      let b:=nestedOddIndexResidue s j t k
      let a:Int:=(2:Int)^(t+3)*((2:Int)^(j+1)-1)
      let q:Int:=nestedOddNumerator (s+6*b) j t/(3:Int)^(k+1)
      b+henselDigit q a*3^k

theorem nestedOddIndexResidue_lt (s j t k:Nat) :
    nestedOddIndexResidue s j t k<3^k := by
  induction k with
  | zero => simp [nestedOddIndexResidue]
  | succ k ih =>
      let b:=nestedOddIndexResidue s j t k
      let a:Int:=(2:Int)^(t+3)*((2:Int)^(j+1)-1)
      let q:Int:=nestedOddNumerator (s+6*b) j t/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hd:d<3:=henselDigit_lt q a
      have hb:b<3^k:=ih
      change b+d*3^k<3^(k+1)
      rw [Nat.pow_succ]
      have hmul:=Nat.mul_lt_mul_of_pos_right hd (Nat.pow_pos (by decide : 0<3))
      omega

/-- The recursively selected index residue really has the required
    3-adic divisibility. -/
theorem nestedOddIndexResidue_good (s j t k:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    (3:Int)^(k+1)∣
      nestedOddNumerator (s+6*nestedOddIndexResidue s j t k) j t := by
  induction k with
  | zero =>
      have hmod:=nestedOddNumerator_sector_mod_three s 0 j t hs hj
      simpa [nestedOddIndexResidue] using
        (Int.dvd_iff_emod_eq_zero.mpr hmod)
  | succ k ih =>
      let b:=nestedOddIndexResidue s j t k
      let a:Int:=(2:Int)^(t+3)*((2:Int)^(j+1)-1)
      let q:Int:=nestedOddNumerator (s+6*b) j t/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hbase:(3:Int)^(k+1)∣nestedOddNumerator (s+6*b) j t:=ih
      have ha:a%3≠0:=by
        simpa [a] using nestedOddCoeff_unit j t hj
      have hd:d<3:=henselDigit_lt q a
      have hdiv:(3:Int)∣q-a*d:=by
        simpa [d] using henselDigit_divides q a ha
      have hgood:(3:Int)^(k+2)∣
          nestedOddNumerator ((s+6*b)+d*depthPeriod (k+1)) j t:=
        (nestedOddNumerator_lift_criterion (s+6*b) j t k d hj hd hbase).mpr
          (by simpa [q,a] using hdiv)
      have hshift:s+6*(b+d*3^k)=
          (s+6*b)+d*depthPeriod (k+1):=by
        simp [depthPeriod,Nat.pow_succ]
        omega
      change (3:Int)^(k+2)∣
        nestedOddNumerator (s+6*(b+d*3^k)) j t
      rw [hshift]
      exact hgood

/-- Exact index-coordinate characterization of every nested odd-parent
    valuation threshold.  For fixed even depth j and exponent t, the
    admissible fatal indices form one residue class modulo 3^k. -/
theorem nestedOddIndexResidue_iff (s j t k h:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    (3:Int)^(k+1)∣nestedOddNumerator (s+6*h) j t ↔
      h%3^k=nestedOddIndexResidue s j t k := by
  induction k generalizing h with
  | zero =>
      have hmod:nestedOddNumerator (s+6*h) j t%3=0 :=
        nestedOddNumerator_sector_mod_three s h j t hs hj
      have hdiv:(3:Int)∣nestedOddNumerator (s+6*h) j t:=
        Int.dvd_iff_emod_eq_zero.mpr hmod
      have hres:h%3^0=nestedOddIndexResidue s j t 0:=by
        simp [nestedOddIndexResidue]
      constructor
      · intro _
        exact hres
      · intro _
        simpa [nestedOddIndexResidue] using hdiv
  | succ k ih =>
      let P:=3^k
      let pn:=3^(k+1)
      let b:=nestedOddIndexResidue s j t k
      let a:Int:=(2:Int)^(t+3)*((2:Int)^(j+1)-1)
      let q:Int:=nestedOddNumerator (s+6*b) j t/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hstep:pn=3*P:=by
        dsimp [pn,P]
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      have hdiv:(3:Int)^(k+1)∣(3:Int)^(k+2):=by
        refine ⟨3,?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz:(3:Int)^(k+2)∣
            nestedOddNumerator (s+6*(h%pn)) j t:=
          (nestedOddNumerator_period_dvd_iff s j t (k+1) h hj).mp hx
        have hlo:(3:Int)^(k+1)∣
            nestedOddNumerator (s+6*(h%pn)) j t:=by
          rcases hz with ⟨w,hw⟩
          rcases hdiv with ⟨v,hv⟩
          refine ⟨v*w,?_⟩
          rw [hw,hv]
          ac_rfl
        have haidx:(h%pn)%P=b:=(ih (h%pn)).mp hlo
        have hp:0<P:=Nat.pow_pos (by decide)
        have hjlt:h%pn<3*P:=by
          have hh:=Nat.mod_lt h (Nat.pow_pos (by decide))
          simpa only [pn,hstep] using hh
        have ht:(h%pn)/P<3:=
          (Nat.div_lt_iff_lt_mul hp).mpr hjlt
        have hsplit:h%pn=(h%pn)%P+((h%pn)/P)*P:=
          Nat.mod_add_div' (h%pn) P
        have hshift:s+6*(h%pn)=
            (s+6*b)+((h%pn)/P)*depthPeriod (k+1):=by
          rw [hsplit,haidx]
          simp [P,depthPeriod,Nat.pow_succ]
          omega
        have hbase:(3:Int)^(k+1)∣nestedOddNumerator (s+6*b) j t:=
          (nestedOddIndexResidue_good s j t k hs hj)
        have hshiftdiv:(3:Int)^(k+2)∣
            nestedOddNumerator
              ((s+6*b)+((h%pn)/P)*depthPeriod (k+1)) j t:=by
          rw [←hshift]
          exact hz
        have hcrit:(3:Int)∣q-a*((h%pn)/P):=
          (nestedOddNumerator_lift_criterion (s+6*b) j t k
            ((h%pn)/P) hj ht hbase).mp hshiftdiv
        have haunit:a%3≠0:=by
          simpa [a] using nestedOddCoeff_unit j t hj
        have hdigit:((h%pn)/P)=d:=
          henselDigit_div q a haunit ((h%pn)/P) ht
            (by simpa [q,a] using hcrit)
        have htarget:h%pn=b+d*P:=by
          rw [hsplit,haidx,hdigit]
        have hnext:nestedOddIndexResidue s j t (k+1)=b+d*P:=rfl
        have hcanon:h%pn=nestedOddIndexResidue s j t (k+1):=by
          rw [hnext]
          exact htarget
        change h%3^(k+1)=nestedOddIndexResidue s j t (k+1)
        simpa [pn] using hcanon
      · intro hx
        have hcanon:h%pn=nestedOddIndexResidue s j t (k+1):=by
          simpa [pn] using hx
        apply (nestedOddNumerator_period_dvd_iff s j t (k+1) h hj).mpr
        rw [hcanon]
        exact nestedOddIndexResidue_good s j t (k+1) hs hj

/-- At each precision the even depth classes in one full depth period
    are in bijection with the fatal-index classes in a surviving sector.
    The inverse maps are the two Hensel selectors above. -/
theorem indexResidue_bijective (s k:Nat) (hs:s=4∨s=5) :
    ∀ h, h<3^k →
      ∃! j, j<depthPeriod k ∧ j%2=0 ∧ indexResidue s j k=h := by
  intro h hh
  let n:=indexSector s h
  let j:=depthResidue n k
  have hn:n%6=4∨n%6=5:=by
    rcases hs with hs4|hs5
    · rw [hs4]; simp [indexSector]
    · rw [hs5]; simp [indexSector]
  have hj:j%2=0:=depthResidue_even n k hn
  have hjlt:j<depthPeriod k:=depthResidue_lt n k
  have hdual:=depth_index_duality s h j k hs hj
  have hmod:j%depthPeriod k=j:=Nat.mod_eq_of_lt hjlt
  have hidx:h%3^k=indexResidue s j k:=hdual.mp hmod
  have hmodh:h%3^k=h:=Nat.mod_eq_of_lt hh
  have hidxeq:indexResidue s j k=h:=hidx.symm.trans hmodh
  refine ⟨j,⟨hjlt,hj,hidxeq⟩,?_⟩
  intro j' hj'
  rcases hj' with ⟨hj'lt,hj'even,hj'idx⟩
  have hdual':j'%depthPeriod k=depthResidue n k ↔
      h%3^k=indexResidue s j' k:=
    depth_index_duality s h j' k hs hj'even
  have hright:h%3^k=indexResidue s j' k:=by
    rw [hj'idx]
    exact hmodh
  have hmod':j'%depthPeriod k=depthResidue n k:=hdual'.mpr hright
  have hjmod:j'%depthPeriod k=j':=Nat.mod_eq_of_lt hj'lt
  calc
    j'=j'%depthPeriod k:=hjmod.symm
    _=depthResidue n k:=hmod'
    _=j:=rfl

#print axioms indexResidue_lt
#print axioms indexResidue_iff
#print axioms depth_index_duality
#print axioms indexResidue_bijective
#print axioms nestedOddNumerator_lift_criterion
#print axioms nestedOddNumerator_unique_lift
#print axioms nestedOddNumerator_sector_mod_three
#print axioms nestedOddIndexResidue_lt
#print axioms nestedOddIndexResidue_good
#print axioms nestedOddIndexResidue_iff
#print axioms tThreeHighGate_digit_eq_quotient_mod_three
#print axioms tThreeSecondParent_index_relation
end CascadeRayIndexHensel
