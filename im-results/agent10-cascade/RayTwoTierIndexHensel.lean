import SignedRayPeriod
import RayDepthHensel
import RayDepthResidue
set_option maxHeartbeats 0

namespace CascadeRayTwoTierIndexHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

private theorem pow_two_mod_three (m:Nat) :
    2^m%3=if m%2=0 then 1 else 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      by_cases hm:m%2=0
      · have hs:(m+1)%2=1:=by omega
        rw [ih,if_pos hm]
        simp [hs]
      · have hs:(m+1)%2=0:=by omega
        rw [ih,if_neg hm]
        simp [hs]

/-- Independent exact index-shift lemma, reproved from the depth period
rather than importing the unfinished RayIndexHensel development. -/
private theorem signedZ_index_shift_digit_mod (n j k t:Nat)
    (ht:t<3) :
    signedZ (n+t*depthPeriod (k+1)) j%(3:Int)^(k+2) =
      (signedZ n j-(3:Int)^(k+1)*
        (4*((2:Int)^(j+1)-1)*t))%(3:Int)^(k+2) := by
  have hpowNat:(2:Nat)^(n+t*depthPeriod (k+1)) =
      (2:Nat)^n*(1+t*3^(k+2)*depthCoeff (k+1)+
        3^(k+3)*depthError (k+1) t) := by
    calc
      (2:Nat)^(n+t*depthPeriod (k+1)) =
          (2:Nat)^n*(2:Nat)^(t*depthPeriod (k+1)) := by
            rw [Nat.pow_add]
      _ = (2:Nat)^n*(1+t*3^(k+2)*depthCoeff (k+1)+
          3^(k+3)*depthError (k+1) t) := by
            rw [pow_period_digit (k+1) t ht]
  have hpowInt:(2:Int)^(n+t*depthPeriod (k+1)) =
      (2:Int)^n*(1+t*(3:Int)^(k+2)*depthCoeff (k+1)+
        (3:Int)^(k+3)*depthError (k+1) t) := by
    exact_mod_cast hpowNat
  have hlin:(2:Int)*(n+t*depthPeriod (k+1))+3 =
      (2:Int)*n+3+4*(3:Int)^(k+1)*t := by
    simp [depthPeriod,Nat.pow_succ]
    omega
  have hz:signedZ (n+t*depthPeriod (k+1)) j =
      signedZ n j-(3:Int)^(k+1)*
        (4*((2:Int)^(j+1)-1)*t)
        +(3:Int)^(k+2)*
          (8*(2:Int)^n*(t*depthCoeff (k+1)+
            3*depthError (k+1) t)) := by
    dsimp [signedZ]
    push_cast
    rw [hpowInt,hlin]
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,
      Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    omega
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  apply Int.emod_eq_zero_of_dvd
  refine ⟨8*(2:Int)^n*(t*depthCoeff (k+1)+
    3*depthError (k+1) t),?_⟩
  rw [hz]
  omega

/-- The exact numerator of the second t=1 gate along a canonical even ray.
If q is the t=1 odd parent of ray(n,j), and w is q's even parent at scale
n-2, then this is exactly 9*(2*w+5). -/
def twoTierNumerator (n j : Nat) : Int :=
  16*signedZ n j - 9*(12*(2:Int)^n + 6*n + 3)

/-- The two-tier numerator has the same one-digit index shift as the
canonical ray numerator, with the unit coefficient multiplied by 16. -/
theorem twoTierNumerator_shift_digit_mod (n j k r : Nat) (hr:r<3) :
    twoTierNumerator (n+r*depthPeriod (k+1)) j%(3:Int)^(k+2) =
      (twoTierNumerator n j-(3:Int)^(k+1)*
        (64*((2:Int)^(j+1)-1)*r))%(3:Int)^(k+2) := by
  let D:=depthPeriod (k+1)
  let P:Int:=(3:Int)^(k+1)
  let M:Int:=(3:Int)^(k+2)
  let n':=n+r*D
  have hp:=pow_period_digit (k+1) r hr
  have hpI:(2:Int)^(r*D)=
      1+(r:Int)*(3:Int)^(k+2)*(depthCoeff (k+1):Int)+
        (3:Int)^(k+3)*(depthError (k+1) r:Int):=by
    exact_mod_cast hp
  have hpowdiv:M∣(2:Int)^(r*D)-1:=by
    refine ⟨(r:Int)*(depthCoeff (k+1):Int)+
      3*(depthError (k+1) r:Int),?_⟩
    rw [hpI]
    dsimp [M]
    rw [show (3:Int)^(k+3)=(3:Int)^(k+2)*3 by
      rw [Int.pow_succ]]
    calc
      1 + r * (3:Int)^(k+2) * (depthCoeff (k+1):Int) +
          (3:Int)^(k+2) * 3 * (depthError (k+1) r:Int) - 1 =
        r * (3:Int)^(k+2) * (depthCoeff (k+1):Int) +
          (3:Int)^(k+2) * 3 * (depthError (k+1) r:Int) := by omega
      _ = (3:Int)^(k+2) *
          (r*(depthCoeff (k+1):Int)+3*(depthError (k+1) r:Int)) := by
        rw [Int.mul_add]
        ac_rfl
  rcases hpowdiv with ⟨c,hc⟩
  have hpowadd:(2:Int)^n'=(2:Int)^n*(2:Int)^(r*D):=by
    dsimp [n']
    rw [Int.pow_add]
  have hpowdiff:(2:Int)^n'-(2:Int)^n=M*((2:Int)^n*c):=by
    rw [hpowadd]
    calc
      (2:Int)^n*(2:Int)^(r*D)-(2:Int)^n =
          (2:Int)^n*((2:Int)^(r*D)-1) := by
            rw [Int.mul_sub]
            simp
      _ = (2:Int)^n*(M*c) := by rw [hc]
      _ = M*((2:Int)^n*c) := by ac_rfl
  have hz:=signedZ_index_shift_digit_mod n j k r hr
  have hZmod:signedZ n' j%M=
      (signedZ n j-P*(4*((2:Int)^(j+1)-1)*r))%M:=by
    simpa [n',D,P,M] using hz
  have hZdiv:M∣signedZ n' j-
      (signedZ n j-P*(4*((2:Int)^(j+1)-1)*r)):=by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hZmod
  have hBdiv:M∣9*(12*((2:Int)^n'-(2:Int)^n)+6*(r:Int)*D):=by
    refine ⟨108*(2:Int)^n*c+36*r,?_⟩
    rw [hpowdiff]
    dsimp [M,D,depthPeriod]
    rw [show (3:Int)^(k+2)=(3:Int)^(k+1)*3 by rw [Int.pow_succ]]
    simp only [Int.mul_add]
    simp
    ac_rfl
  have hAeq:twoTierNumerator n' j-
      (twoTierNumerator n j-P*
        (64*((2:Int)^(j+1)-1)*r)) =
      16*(signedZ n' j-
        (signedZ n j-P*(4*((2:Int)^(j+1)-1)*r)))-
        9*(12*((2:Int)^n'-(2:Int)^n)+6*(r:Int)*D):=by
    simp [twoTierNumerator,n']
    omega
  rcases hZdiv with ⟨z,hzdiv⟩
  rcases hBdiv with ⟨b,hbdiv⟩
  have hdiv:M∣twoTierNumerator n' j-
      (twoTierNumerator n j-P*
        (64*((2:Int)^(j+1)-1)*r)):=by
    refine ⟨16*z-b,?_⟩
    rw [hAeq,hzdiv,hbdiv]
    rw [Int.mul_sub]
    ac_rfl
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  exact Int.dvd_iff_emod_eq_zero.mp hdiv

/-- The exact next-digit criterion for the second-tier gate. -/
private theorem twoTierNumerator_lift_criterion (n j k r : Nat)
    (hr:r<3)
    (hbase:(3:Int)^(k+1)∣twoTierNumerator n j) :
    (3:Int)^(k+2)∣twoTierNumerator
        (n+r*depthPeriod (k+1)) j ↔
      (3:Int)∣
        (twoTierNumerator n j/(3:Int)^(k+1)-
          (64*((2:Int)^(j+1)-1)*r)) := by
  let P:Int:=(3:Int)^(k+1)
  let M:Int:=(3:Int)^(k+2)
  let a:Int:=64*((2:Int)^(j+1)-1)
  have hp:P≠0:=by
    dsimp [P]
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM:M=3*P:=by
    dsimp [M,P]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hmod:=twoTierNumerator_shift_digit_mod n j k r hr
  have hmod':twoTierNumerator (n+r*depthPeriod (k+1)) j%M=
      (twoTierNumerator n j-P*(a*r))%M:=by
    simpa [P,M,a,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using hmod
  have hdiviff:M∣twoTierNumerator (n+r*depthPeriod (k+1)) j ↔
      M∣(twoTierNumerator n j-P*(a*r)):=by
    rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero,hmod']
  have hquot:P*(twoTierNumerator n j/P)=twoTierNumerator n j:=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor:twoTierNumerator n j-P*(a*r)=
      P*(twoTierNumerator n j/P-a*r):=by
    calc
      _=P*(twoTierNumerator n j/P)-P*(a*r):=by rw [hquot]
      _=P*(twoTierNumerator n j/P-a*r):=by rw [Int.mul_sub]
  rw [hdiviff,hfactor,hM]
  exact Int.mul_dvd_mul_iff_left hp

/-- The two-tier lift coefficient is a 3-adic unit at every even depth. -/
theorem twoTierCoeff_mod_three (j:Nat) (hj:j%2=0) :
    (64*((2:Int)^(j+1)-1))%3=1 := by
  have hodd:(j+1)%2=1:=by omega
  have hpNat:(2:Nat)^(j+1)%3=2:=by
    rw [pow_two_mod_three]
    simp [hodd]
  have hpInt:((2:Int)^(j+1))%3=2:=by
    exact_mod_cast hpNat
  have hminus:((2:Int)^(j+1)-1)%3=1:=by
    rw [Int.sub_emod,hpInt]
    decide
  calc
    (64*((2:Int)^(j+1)-1))%3 =
        ((64:Int)%3)*(((2:Int)^(j+1)-1)%3)%3:=by
          rw [Int.mul_emod]
    _=1:=by rw [hminus]; decide

/-- Every surviving fatal sector starts the second-tier numerator in
the zero class modulo three. -/
theorem twoTierNumerator_sector_mod_three (s h j:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    twoTierNumerator (s+6*h) j%3=0 := by
  have hsector:(s+6*h)%6=4∨(s+6*h)%6=5:=by
    rcases hs with hs4|hs5
    · rw [hs4]; simp
    · rw [hs5]; simp
  have hZmod:signedZ (s+6*h) j%3=0:=
    (signedZ_mod_three_even_iff (s+6*h) j hsector).mpr hj
  have hZdiv:(3:Int)∣signedZ (s+6*h) j:=
    Int.dvd_iff_emod_eq_zero.mpr hZmod
  rcases hZdiv with ⟨z,hz⟩
  have hdiv:(3:Int)∣twoTierNumerator (s+6*h) j:=by
    refine ⟨16*z-3*(12*(2:Int)^(s+6*h)+6*(s+6*h)+3),?_⟩
    dsimp [twoTierNumerator]
    rw [hz]
    rw [Int.mul_sub]
    simp [Int.mul_assoc]
  exact Int.dvd_iff_emod_eq_zero.mp hdiv

/-- Precisely one of the three next index digits lifts the second-tier
numerator by one additional power of three. -/
theorem twoTierNumerator_unique_lift (n j k:Nat)
    (hj:j%2=0)
    (hbase:(3:Int)^(k+1)∣twoTierNumerator n j) :
    ∃! r, r<3 ∧
      (3:Int)^(k+2)∣twoTierNumerator
        (n+r*depthPeriod (k+1)) j := by
  let q:Int:=twoTierNumerator n j/(3:Int)^(k+1)
  let a:Int:=64*((2:Int)^(j+1)-1)
  let d:=henselDigit q a
  have ha:a%3≠0:=by
    rw [show a%3=1 by simpa [a] using twoTierCoeff_mod_three j hj]
    decide
  have hd:d<3:=henselDigit_lt q a
  have hdiv:(3:Int)∣q-a*d:=by
    simpa [d] using henselDigit_divides q a ha
  have hgood:(3:Int)^(k+2)∣
      twoTierNumerator (n+d*depthPeriod (k+1)) j:=
    (twoTierNumerator_lift_criterion n j k d hd hbase).mpr
      (by simpa [q,a] using hdiv)
  refine ⟨d,⟨hd,hgood⟩,?_⟩
  intro r hr
  rcases hr with ⟨hrlt,hrdiv⟩
  have hcrit:(3:Int)∣q-a*r:=
    (twoTierNumerator_lift_criterion n j k r hrlt hbase).mp hrdiv
  exact henselDigit_div q a ha r hrlt (by simpa [q,a] using hcrit)

/-- Recursive index selector for the second-tier gate. -/
def twoTierIndexResidue (s j:Nat) : Nat→Nat
  | 0 => 0
  | k+1 =>
      let b:=twoTierIndexResidue s j k
      let a:Int:=64*((2:Int)^(j+1)-1)
      let q:Int:=twoTierNumerator (s+6*b) j/(3:Int)^(k+1)
      b+henselDigit q a*3^k

theorem twoTierIndexResidue_lt (s j k:Nat) :
    twoTierIndexResidue s j k<3^k:=by
  induction k with
  | zero => simp [twoTierIndexResidue]
  | succ k ih =>
      let b:=twoTierIndexResidue s j k
      let a:Int:=64*((2:Int)^(j+1)-1)
      let q:Int:=twoTierNumerator (s+6*b) j/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hd:d<3:=henselDigit_lt q a
      have hb:b<3^k:=ih
      change b+d*3^k<3^(k+1)
      rw [Nat.pow_succ]
      have hmul:=Nat.mul_lt_mul_of_pos_right hd (Nat.pow_pos (by decide : 0<3))
      omega

/-- The recursively selected second-tier index really has the required
3-adic divisibility. -/
theorem twoTierIndexResidue_good (s j k:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    (3:Int)^(k+1)∣
      twoTierNumerator (s+6*twoTierIndexResidue s j k) j := by
  induction k with
  | zero =>
      have hmod:=twoTierNumerator_sector_mod_three s 0 j hs hj
      simpa [twoTierIndexResidue] using
        (Int.dvd_iff_emod_eq_zero.mpr hmod)
  | succ k ih =>
      let b:=twoTierIndexResidue s j k
      let a:Int:=64*((2:Int)^(j+1)-1)
      let q:Int:=twoTierNumerator (s+6*b) j/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hbase:(3:Int)^(k+1)∣twoTierNumerator (s+6*b) j:=ih
      have ha:a%3≠0:=by
        rw [show a%3=1 by simpa [a] using twoTierCoeff_mod_three j hj]
        decide
      have hd:d<3:=henselDigit_lt q a
      have hdiv:(3:Int)∣q-a*d:=by
        simpa [d] using henselDigit_divides q a ha
      have hgood:(3:Int)^(k+2)∣
          twoTierNumerator ((s+6*b)+d*depthPeriod (k+1)) j:=
        (twoTierNumerator_lift_criterion (s+6*b) j k d hd hbase).mpr
          (by simpa [q,a] using hdiv)
      have hshift:s+6*(b+d*3^k)=
          (s+6*b)+d*depthPeriod (k+1):=by
        simp [depthPeriod,Nat.pow_succ]
        omega
      change (3:Int)^(k+2)∣
        twoTierNumerator (s+6*(b+d*3^k)) j
      rw [hshift]
      exact hgood

private theorem twoTierNumerator_step_divisible (n j k:Nat) :
    (3:Int)^(k+1)∣
      twoTierNumerator (n+depthPeriod (k+1)) j-
        twoTierNumerator n j :=by
  let P:Int:=(3:Int)^(k+1)
  let M:Int:=(3:Int)^(k+2)
  let a:Int:=64*((2:Int)^(j+1)-1)
  have hmod:=twoTierNumerator_shift_digit_mod n j k 1 (by decide)
  have hdiv:M∣twoTierNumerator (n+depthPeriod (k+1)) j-
      (twoTierNumerator n j-P*a):=by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp
      (by simpa [P,M,a] using hmod)
  rcases hdiv with ⟨z,hz⟩
  have hM:M=3*P:=by
    dsimp [M,P]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  refine ⟨3*z-a,?_⟩
  calc
    twoTierNumerator (n+depthPeriod (k+1)) j-twoTierNumerator n j =
        (twoTierNumerator (n+depthPeriod (k+1)) j-
          (twoTierNumerator n j-P*a))-P*a:=by omega
    _=M*z-P*a:=by rw [hz]
    _=P*(3*z-a):=by
      rw [hM]
      rw [Int.mul_sub]
      ac_rfl

private theorem twoTierNumerator_period_mul (s j k h m:Nat) :
    twoTierNumerator (s+6*(h+m*3^k)) j%(3:Int)^(k+1)=
      twoTierNumerator (s+6*h) j%(3:Int)^(k+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hshift:s+6*(h+(m+1)*3^k)=
          (s+6*(h+m*3^k))+depthPeriod (k+1):=by
        simp [depthPeriod,Nat.pow_succ]
        omega
      rw [hshift]
      calc
        twoTierNumerator ((s+6*(h+m*3^k))+depthPeriod (k+1)) j%
            (3:Int)^(k+1)=
          twoTierNumerator (s+6*(h+m*3^k)) j%(3:Int)^(k+1):=by
            apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
            exact Int.dvd_iff_emod_eq_zero.mp
              (twoTierNumerator_step_divisible (s+6*(h+m*3^k)) j k)
        _=twoTierNumerator (s+6*h) j%(3:Int)^(k+1):=ih

private theorem twoTierNumerator_period_dvd_iff (s j k h m:Nat) :
    (3:Int)^(k+1)∣twoTierNumerator (s+6*(h+m*3^k)) j ↔
      (3:Int)^(k+1)∣twoTierNumerator (s+6*h) j := by
  rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero]
  exact twoTierNumerator_period_mul s j k h m

private theorem twoTierNumerator_period_mod_dvd_iff (s j k h:Nat) :
    (3:Int)^(k+1)∣twoTierNumerator (s+6*h) j ↔
      (3:Int)^(k+1)∣twoTierNumerator (s+6*(h%3^k)) j := by
  have hper:=twoTierNumerator_period_dvd_iff s j k (h%3^k) (h/3^k)
  have heq:h%3^k+(h/3^k)*3^k=h:=Nat.mod_add_div' h (3^k)
  rw [heq] at hper
  exact hper

/-- Exact index-coordinate characterization of the second-tier gate:
for fixed even depth j, admissible fatal indices form one residue class
modulo 3^k at every precision k. -/
theorem twoTierIndexResidue_iff (s j k h:Nat)
    (hs:s=4∨s=5) (hj:j%2=0) :
    (3:Int)^(k+1)∣twoTierNumerator (s+6*h) j ↔
      h%3^k=twoTierIndexResidue s j k := by
  induction k generalizing h with
  | zero =>
      have hmod:twoTierNumerator (s+6*h) j%3=0:=
        twoTierNumerator_sector_mod_three s h j hs hj
      have hdiv:(3:Int)∣twoTierNumerator (s+6*h) j:=
        Int.dvd_iff_emod_eq_zero.mpr hmod
      have hres:h%3^0=twoTierIndexResidue s j 0:=by
        simp [twoTierIndexResidue]
      constructor
      · intro _
        exact hres
      · intro _
        simpa [twoTierIndexResidue] using hdiv
  | succ k ih =>
      let P:=3^k
      let pn:=3^(k+1)
      let b:=twoTierIndexResidue s j k
      let a:Int:=64*((2:Int)^(j+1)-1)
      let q:Int:=twoTierNumerator (s+6*b) j/(3:Int)^(k+1)
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
            twoTierNumerator (s+6*(h%pn)) j:=
          (twoTierNumerator_period_mod_dvd_iff s j (k+1) h).mp hx
        have hlo:(3:Int)^(k+1)∣
            twoTierNumerator (s+6*(h%pn)) j:=by
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
        have hbase:(3:Int)^(k+1)∣twoTierNumerator (s+6*b) j:=
          twoTierIndexResidue_good s j k hs hj
        have hshiftdiv:(3:Int)^(k+2)∣
            twoTierNumerator
              ((s+6*b)+((h%pn)/P)*depthPeriod (k+1)) j:=by
          rw [←hshift]
          exact hz
        have hcrit:(3:Int)∣q-a*((h%pn)/P):=
          (twoTierNumerator_lift_criterion (s+6*b) j k
            ((h%pn)/P) ht hbase).mp hshiftdiv
        have haunit:a%3≠0:=by
          rw [show a%3=1 by simpa [a] using twoTierCoeff_mod_three j hj]
          decide
        have hdigit:((h%pn)/P)=d:=
          henselDigit_div q a haunit ((h%pn)/P) ht
            (by simpa [q,a] using hcrit)
        have htarget:h%pn=b+d*P:=by
          rw [hsplit,haidx,hdigit]
        have hnext:twoTierIndexResidue s j (k+1)=b+d*P:=rfl
        have hcanon:h%pn=twoTierIndexResidue s j (k+1):=by
          rw [hnext]
          exact htarget
        change h%3^(k+1)=twoTierIndexResidue s j (k+1)
        simpa [pn] using hcanon
      · intro hx
        have hcanon:h%pn=twoTierIndexResidue s j (k+1):=by
          simpa [pn] using hx
        apply (twoTierNumerator_period_mod_dvd_iff s j (k+1) h).mpr
        rw [hcanon]
        exact twoTierIndexResidue_good s j (k+1) hs hj

/-- Algebraic bridge to the source parent graph. If d is the odd quotient
for a t=1 parent q of a canonical ray node and w is q's even parent at
the same dyadic scale n-2, then T(n,j)=9*(2*w+5). -/
theorem twoTierNumerator_parent_identity (n j:Nat) (d q w:Int)
    (hn:2≤n)
    (hz:signedZ n j=9*d)
    (hq:4*d=8*(2:Int)^(n-2)+q+(n-2)+5)
    (hw:2*q=8*(2:Int)^(n-2)+w+(n-2)) :
    twoTierNumerator n j=9*(2*w+5) := by
  have hp:8*(2:Int)^(n-2)=2*(2:Int)^n:=by
    have he:n=(n-2)+2:=by omega
    have hpow:(2:Int)^n=4*(2:Int)^(n-2):=by
      rw [he,Int.pow_add]
      decide
    omega
  dsimp [twoTierNumerator]
  rw [hz]
  omega

#print axioms twoTierNumerator_shift_digit_mod
#print axioms twoTierNumerator_lift_criterion
#print axioms twoTierNumerator_unique_lift
#print axioms twoTierNumerator_sector_mod_three
#print axioms twoTierIndexResidue_good
#print axioms twoTierIndexResidue_iff
#print axioms twoTierNumerator_parent_identity
end CascadeRayTwoTierIndexHensel
