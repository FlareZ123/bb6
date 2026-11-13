import SignedRayPeriod
import RayDepthHensel
import RayDepthResidue

set_option maxHeartbeats 0

namespace CascadeQStateIndexHensel

open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

/-- The Q-state numerator obtained from the signed ray coordinate. -/
def qNumerator (n j : Nat) : Int :=
  8*signedZ n j - 9*((2:Int)^(n+2)+2*n+1)

/-- Expanded affine form of the Q-state numerator. -/
theorem qNumerator_expanded (n j : Nat) :
    qNumerator n j =
      28*(2:Int)^n - 2*n + 15 - (2:Int)^(j+4)*(2*n+3) := by
  dsimp [qNumerator, signedZ]
  push_cast
  rw [Int.pow_add, Int.pow_add]
  ring

/-- The direct Q coefficient differs by 36 from the coefficient obtained
by multiplying the signedZ index shift by eight. -/
def qIndexCoefficient (j : Nat) : Int :=
  4*(1+(2:Int)^(j+4))

theorem qIndexCoefficient_eq_signedZ (j : Nat) :
    qIndexCoefficient j =
      32*((2:Int)^(j+1)-1)+36 := by
  have hp : (2:Int)^(j+4)=8*(2:Int)^(j+1) := by
    have he : j+4=(j+1)+3 := by omega
    rw [he,Int.pow_add]
    norm_num
    ring
  dsimp [qIndexCoefficient]
  rw [hp]
  ring

private theorem pow_two_mod_three (m : Nat) :
    2^m%3 = if m%2=0 then 1 else 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      by_cases hm : m%2=0
      · have hs : (m+1)%2=1 := by omega
        rw [ih,if_pos hm]
        simp [hs]
      · have hs : (m+1)%2=0 := by omega
        rw [ih,if_neg hm]
        simp [hs]

/-- The direct Q coefficient is a unit modulo three for every even depth. -/
theorem qIndexCoefficient_mod_three (j : Nat) (hj : j%2=0) :
    qIndexCoefficient j%3=2 := by
  have heven : (j+4)%2=0 := by omega
  have hpNat : (2:Nat)^(j+4)%3=1 := by
    rw [pow_two_mod_three]
    simp [heven]
  have hpInt : ((2:Int)^(j+4))%3=1 := by
    exact_mod_cast hpNat
  dsimp [qIndexCoefficient]
  rw [Int.mul_emod,Int.add_emod,hpInt]
  norm_num

/-- One index digit has the exact Q shift congruence.  The coefficient
is the direct-Q coefficient 4*(1+2^(j+4)); it is congruent modulo 3
to 32*(2^(j+1)-1), the coefficient obtained from signedZ alone. -/
theorem qNumerator_shift_digit_mod (n j k r : Nat) (hr : r<3) :
    qNumerator (n+r*depthPeriod (k+1)) j%(3:Int)^(k+2) =
      (qNumerator n j-(3:Int)^(k+1)*(qIndexCoefficient j*r))%
        (3:Int)^(k+2) := by
  let D := depthPeriod (k+1)
  let P : Int := (3:Int)^(k+1)
  let M : Int := (3:Int)^(k+2)
  let n' := n+r*D
  have hp := pow_period_digit (k+1) r hr
  have hpI : (2:Int)^(r*D) =
      1+(r:Int)*(3:Int)^(k+2)*(depthCoeff (k+1):Int)+
        (3:Int)^(k+3)*(depthError (k+1) r:Int) := by
    exact_mod_cast hp
  have hpowdiv : M∣(2:Int)^(r*D)-1 := by
    refine ⟨(r:Int)*(depthCoeff (k+1):Int)+
      3*(depthError (k+1) r:Int),?_⟩
    rw [hpI]
    dsimp [M]
    rw [show (3:Int)^(k+3)=(3:Int)^(k+2)*3 by
      rw [Int.pow_succ]]
    ring
  rcases hpowdiv with ⟨c,hc⟩
  have hpowadd : (2:Int)^n'=(2:Int)^n*(2:Int)^(r*D) := by
    dsimp [n']
    rw [Int.pow_add]
  have hpowdiff : (2:Int)^n'-(2:Int)^n=M*((2:Int)^n*c) := by
    rw [hpowadd,hc]
    ring
  have hlin : (2:Int)*n' =
      (2:Int)*n+4*(3:Int)^(k+1)*r := by
    dsimp [n',D,depthPeriod]
    simp [Nat.pow_succ]
    push_cast
    ring
  have hAeq : qNumerator n' j-
      (qNumerator n j-P*(qIndexCoefficient j*r)) =
      28*((2:Int)^n'-(2:Int)^n) := by
    rw [qNumerator_expanded,qNumerator_expanded]
    dsimp [qIndexCoefficient]
    simp_rw [hlin]
    ring
  have hdiv : M∣qNumerator n' j-
      (qNumerator n j-P*(qIndexCoefficient j*r)) := by
    refine ⟨28*(2:Int)^n*c,?_⟩
    rw [hAeq,hpowdiff]
    ring
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  exact Int.dvd_iff_emod_eq_zero.mp hdiv

/-- The exact next-digit criterion for the Q-state numerator. -/
theorem qNumerator_lift_criterion (n j k r : Nat)
    (hr : r<3)
    (hbase : (3:Int)^(k+1)∣qNumerator n j) :
    (3:Int)^(k+2)∣qNumerator
        (n+r*depthPeriod (k+1)) j ↔
      (3:Int)∣
        (qNumerator n j/(3:Int)^(k+1)-
          (qIndexCoefficient j*r)) := by
  let P : Int := (3:Int)^(k+1)
  let M : Int := (3:Int)^(k+2)
  let a : Int := qIndexCoefficient j
  have hp : P≠0 := by
    dsimp [P]
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM : M=3*P := by
    dsimp [M,P]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hmod := qNumerator_shift_digit_mod n j k r hr
  have hmod' : qNumerator (n+r*depthPeriod (k+1)) j%M =
      (qNumerator n j-P*(a*r))%M := by
    simpa [P,M,a,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using hmod
  have hdiviff : M∣qNumerator (n+r*depthPeriod (k+1)) j ↔
      M∣(qNumerator n j-P*(a*r)) := by
    rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero,hmod']
  have hquot : P*(qNumerator n j/P)=qNumerator n j :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor : qNumerator n j-P*(a*r)=
      P*(qNumerator n j/P-a*r) := by
    calc
      _=P*(qNumerator n j/P)-P*(a*r) := by rw [hquot]
      _=P*(qNumerator n j/P-a*r) := by rw [Int.mul_sub]
  rw [hdiviff,hfactor,hM]
  exact Int.mul_dvd_mul_iff_left hp

/-- The three possible next index digits have exactly one successful lift. -/
theorem qNumerator_unique_lift (n j k : Nat)
    (hj : j%2=0)
    (hbase : (3:Int)^(k+1)∣qNumerator n j) :
    ∃! r, r<3 ∧
      (3:Int)^(k+2)∣qNumerator
        (n+r*depthPeriod (k+1)) j := by
  let q : Int := qNumerator n j/(3:Int)^(k+1)
  let a : Int := qIndexCoefficient j
  let d := henselDigit q a
  have ha : a%3≠0 := by
    rw [show a%3=2 by simpa [a] using qIndexCoefficient_mod_three j hj]
    norm_num
  have hd : d<3 := henselDigit_lt q a
  have hdiv : (3:Int)∣q-a*d := by
    simpa [d] using henselDigit_divides q a ha
  have hgood : (3:Int)^(k+2)∣
      qNumerator (n+d*depthPeriod (k+1)) j :=
    (qNumerator_lift_criterion n j k d hd hbase).mpr
      (by simpa [q,a] using hdiv)
  refine ⟨d,⟨hd,hgood⟩,?_⟩
  intro r hr
  rcases hr with ⟨hrlt,hrdiv⟩
  have hcrit : (3:Int)∣q-a*r :=
    (qNumerator_lift_criterion n j k r hrlt hbase).mp hrdiv
  exact henselDigit_div q a ha r hrlt (by simpa [q,a] using hcrit)

/-- The base Q-state numerator is divisible by three in both surviving
index sectors whenever the ray depth j is even. -/
theorem qNumerator_sector_mod_three (s h j : Nat)
    (hs : s=4∨s=5) (hj : j%2=0) :
    qNumerator (s+6*h) j%3=0 := by
  have hsector : (s+6*h)%6=4∨(s+6*h)%6=5 := by
    rcases hs with hs4|hs5
    · rw [hs4]
      simp
    · rw [hs5]
      simp
  have hZmod : signedZ (s+6*h) j%3=0 :=
    (signedZ_mod_three_even_iff (s+6*h) j hsector).mpr hj
  have hZdiv : (3:Int)∣signedZ (s+6*h) j :=
    Int.dvd_iff_emod_eq_zero.mpr hZmod
  rcases hZdiv with ⟨z,hz⟩
  have hQdiv : (3:Int)∣qNumerator (s+6*h) j := by
    refine ⟨8*z-3*((2:Int)^(s+6*h+2)+2*(s+6*h)+1),?_⟩
    dsimp [qNumerator]
    rw [hz]
    ring
  exact Int.dvd_iff_emod_eq_zero.mp hQdiv

/-- Recursive index selector: for fixed even depth j and sector s=4 or 5,
this returns the unique index h modulo 3^k for divisibility by 3^(k+1). -/
def qIndexResidue (s j : Nat) : Nat→Nat
  | 0 => 0
  | k+1 =>
      let b := qIndexResidue s j k
      let a : Int := qIndexCoefficient j
      let q : Int := qNumerator (s+6*b) j/(3:Int)^(k+1)
      b+henselDigit q a*3^k

theorem qIndexResidue_lt (s j k : Nat) :
    qIndexResidue s j k<3^k := by
  induction k with
  | zero =>
      simp [qIndexResidue]
  | succ k ih =>
      let b := qIndexResidue s j k
      let a : Int := qIndexCoefficient j
      let q : Int := qNumerator (s+6*b) j/(3:Int)^(k+1)
      let d := henselDigit q a
      have hd : d<3 := henselDigit_lt q a
      have hb : b<3^k := ih
      change b+d*3^k<3^(k+1)
      rw [Nat.pow_succ]
      have hmul := Nat.mul_lt_mul_of_pos_right hd
        (Nat.pow_pos (by decide : 0<3))
      omega

/-- The recursively selected index residue has the required Q divisibility. -/
theorem qIndexResidue_good (s j k : Nat)
    (hs : s=4∨s=5) (hj : j%2=0) :
    (3:Int)^(k+1)∣
      qNumerator (s+6*qIndexResidue s j k) j := by
  induction k with
  | zero =>
      have hmod := qNumerator_sector_mod_three s 0 j hs hj
      have hdiv : (3:Int)∣qNumerator s j :=
        Int.dvd_iff_emod_eq_zero.mpr hmod
      simpa [qIndexResidue] using hdiv
  | succ k ih =>
      let b := qIndexResidue s j k
      let a : Int := qIndexCoefficient j
      let q : Int := qNumerator (s+6*b) j/(3:Int)^(k+1)
      let d := henselDigit q a
      have hbase : (3:Int)^(k+1)∣qNumerator (s+6*b) j := ih
      have ha : a%3≠0 := by
        rw [show a%3=2 by simpa [a] using qIndexCoefficient_mod_three j hj]
        norm_num
      have hd : d<3 := henselDigit_lt q a
      have hdiv : (3:Int)∣q-a*d := by
        simpa [d] using henselDigit_divides q a ha
      have hgood : (3:Int)^(k+2)∣
          qNumerator ((s+6*b)+d*depthPeriod (k+1)) j :=
        (qNumerator_lift_criterion (s+6*b) j k d hd hbase).mpr
          (by simpa [q,a] using hdiv)
      have hshift : s+6*(b+d*3^k)=
          (s+6*b)+d*depthPeriod (k+1) := by
        simp [depthPeriod,Nat.pow_succ]
        omega
      change (3:Int)^(k+2)∣
        qNumerator (s+6*(b+d*3^k)) j
      rw [hshift]
      exact hgood

private theorem qNumerator_step_divisible (n j k : Nat) :
    (3:Int)^(k+1)∣
      qNumerator (n+depthPeriod (k+1)) j-qNumerator n j := by
  let P : Int := (3:Int)^(k+1)
  let M : Int := (3:Int)^(k+2)
  let a : Int := qIndexCoefficient j
  have hmod := qNumerator_shift_digit_mod n j k 1 (by decide)
  have hdiv : M∣qNumerator (n+depthPeriod (k+1)) j-
      (qNumerator n j-P*a) := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp
      (by simpa [P,M,a] using hmod)
  rcases hdiv with ⟨z,hz⟩
  have hM : M=3*P := by
    dsimp [M,P]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  refine ⟨3*z-a,?_⟩
  calc
    qNumerator (n+depthPeriod (k+1)) j-qNumerator n j =
        (qNumerator (n+depthPeriod (k+1)) j-
          (qNumerator n j-P*a))-P*a := by ring
    _=M*z-P*a := by rw [hz]
    _=P*(3*z-a) := by rw [hM]; ring

private theorem qNumerator_period_mul (s j k h m : Nat) :
    qNumerator (s+6*(h+m*3^k)) j%(3:Int)^(k+1)=
      qNumerator (s+6*h) j%(3:Int)^(k+1) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hshift : s+6*(h+(m+1)*3^k)=
          (s+6*(h+m*3^k))+depthPeriod (k+1) := by
        simp [depthPeriod,Nat.pow_succ]
        omega
      rw [hshift]
      calc
        qNumerator ((s+6*(h+m*3^k))+depthPeriod (k+1)) j%
            (3:Int)^(k+1)=
          qNumerator (s+6*(h+m*3^k)) j%(3:Int)^(k+1) := by
            apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
            exact Int.dvd_iff_emod_eq_zero.mp
              (qNumerator_step_divisible (s+6*(h+m*3^k)) j k)
        _=qNumerator (s+6*h) j%(3:Int)^(k+1) := ih

private theorem qNumerator_period_dvd_iff (s j k h m : Nat) :
    (3:Int)^(k+1)∣qNumerator (s+6*(h+m*3^k)) j ↔
      (3:Int)^(k+1)∣qNumerator (s+6*h) j := by
  rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero]
  exact qNumerator_period_mul s j k h m

private theorem qNumerator_period_mod_dvd_iff (s j k h : Nat) :
    (3:Int)^(k+1)∣qNumerator (s+6*h) j ↔
      (3:Int)^(k+1)∣qNumerator (s+6*(h%3^k)) j := by
  have hper := qNumerator_period_dvd_iff s j k (h%3^k) (h/3^k)
  have heq : h%3^k+(h/3^k)*3^k=h := Nat.mod_add_div' h (3^k)
  rw [heq] at hper
  exact hper

/-- Exact index-coordinate characterization: for fixed even depth j,
the admissible indices in either surviving sector form one residue
class modulo 3^k at every precision k. -/
theorem qIndexResidue_iff (s j k h : Nat)
    (hs : s=4∨s=5) (hj : j%2=0) :
    (3:Int)^(k+1)∣qNumerator (s+6*h) j ↔
      h%3^k=qIndexResidue s j k := by
  induction k generalizing h with
  | zero =>
      have hmod : qNumerator (s+6*h) j%3=0 :=
        qNumerator_sector_mod_three s h j hs hj
      have hdiv : (3:Int)∣qNumerator (s+6*h) j :=
        Int.dvd_iff_emod_eq_zero.mpr hmod
      have hres : h%3^0=qIndexResidue s j 0 := by
        simp [qIndexResidue]
      constructor
      · intro _
        exact hres
      · intro _
        simpa [qIndexResidue] using hdiv
  | succ k ih =>
      let P := 3^k
      let pn := 3^(k+1)
      let b := qIndexResidue s j k
      let a : Int := qIndexCoefficient j
      let q : Int := qNumerator (s+6*b) j/(3:Int)^(k+1)
      let d := henselDigit q a
      have hstep : pn=3*P := by
        dsimp [pn,P]
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      have hdiv : (3:Int)^(k+1)∣(3:Int)^(k+2) := by
        refine ⟨3,?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz : (3:Int)^(k+2)∣
            qNumerator (s+6*(h%pn)) j :=
          (qNumerator_period_mod_dvd_iff s j (k+1) h).mp hx
        have hlo : (3:Int)^(k+1)∣
            qNumerator (s+6*(h%pn)) j := by
          rcases hz with ⟨w,hw⟩
          rcases hdiv with ⟨v,hv⟩
          refine ⟨v*w,?_⟩
          rw [hw,hv]
          ac_rfl
        have haidx : (h%pn)%P=b := (ih (h%pn)).mp hlo
        have hp : 0<P := Nat.pow_pos (by decide)
        have hjlt : h%pn<3*P := by
          have hh := Nat.mod_lt h (Nat.pow_pos (by decide))
          simpa only [pn,hstep] using hh
        have ht : (h%pn)/P<3 :=
          (Nat.div_lt_iff_lt_mul hp).mpr hjlt
        have hsplit : h%pn=(h%pn)%P+((h%pn)/P)*P :=
          Nat.mod_add_div' (h%pn) P
        have hshift : s+6*(h%pn)=
            (s+6*b)+((h%pn)/P)*depthPeriod (k+1) := by
          rw [hsplit,haidx]
          simp [P,depthPeriod,Nat.pow_succ]
          omega
        have hbase : (3:Int)^(k+1)∣qNumerator (s+6*b) j :=
          qIndexResidue_good s j k hs hj
        have hshiftdiv : (3:Int)^(k+2)∣
            qNumerator ((s+6*b)+((h%pn)/P)*depthPeriod (k+1)) j := by
          rw [←hshift]
          exact hz
        have hcrit : (3:Int)∣q-a*((h%pn)/P) :=
          (qNumerator_lift_criterion (s+6*b) j k
            ((h%pn)/P) ht hbase).mp hshiftdiv
        have haunit : a%3≠0 := by
          rw [show a%3=2 by simpa [a] using qIndexCoefficient_mod_three j hj]
          norm_num
        have hdigit : (h%pn)/P=d :=
          henselDigit_div q a haunit ((h%pn)/P) ht
            (by simpa [q,a] using hcrit)
        have htarget : h%pn=b+d*P := by
          rw [hsplit,haidx,hdigit]
        have hnext : qIndexResidue s j (k+1)=b+d*P := rfl
        have hcanon : h%pn=qIndexResidue s j (k+1) := by
          rw [hnext]
          exact htarget
        change h%3^(k+1)=qIndexResidue s j (k+1)
        simpa [pn] using hcanon
      · intro hx
        have hcanon : h%pn=qIndexResidue s j (k+1) := by
          simpa [pn] using hx
        apply (qNumerator_period_mod_dvd_iff s j (k+1) h).mpr
        rw [hcanon]
        exact qIndexResidue_good s j (k+1) hs hj

/-- All-index form for n mod 6 in {4,5}. -/
theorem qIndexResidue_all_sectors_iff (n j k : Nat)
    (hn : n%6=4∨n%6=5) (hj : j%2=0) :
    (3:Int)^(k+1)∣qNumerator n j ↔
      (n/6)%3^k=qIndexResidue (n%6) j k := by
  let s := n%6
  let h := n/6
  have hs : s=4∨s=5 := by simpa [s] using hn
  have hdecomp : s+6*h=n := by
    dsimp [s,h]
    have h' := Nat.mod_add_div' n 6
    omega
  have hmain := qIndexResidue_iff s j k h hs hj
  simpa [s,h,hdecomp] using hmain

/-- The 887 family is the sector-5 specialization
n=5+6*(147+2187*r). -/
theorem qIndexResidue_887_iff (r j k : Nat) (hj : j%2=0) :
    (3:Int)^(k+1)∣qNumerator (887+13122*r) j ↔
      (147+2187*r)%3^k=qIndexResidue 5 j k := by
  have hidx : 887+13122*r=5+6*(147+2187*r) := by omega
  rw [hidx]
  exact qIndexResidue_iff 5 j k (147+2187*r) (by decide) hj

/-- Source-coordinate identity for the actual t=1 odd-parent arm at
scale n-2.  The hypotheses are exactly its odd quotient, odd-band
condition, source-height equation, and parent output equation.  The
signed source coordinate is signedZ(n,j)=2*u+5. -/
theorem qNumerator_t1_parent_identity (n j u q d : Nat)
    (hn : 2≤n)
    (hSigned : signedZ n j=(2*u+5:Int))
    (hd : d%2=1)
    (hband : 6*2^(n-2)+1≤2*d ∧ 2*d≤8*2^(n-2)-1)
    (hodd : 2*u+5=9*d)
    (hparent : 2*(2*d)=8*2^(n-2)+q+(n-2)+5) :
    qNumerator n j=9*(2*q+5) := by
  have hz : signedZ n j=9*(d:Int) := by
    rw [hSigned]
    exact_mod_cast hodd
  have hparentI : 4*(d:Int)=
      8*(2:Int)^(n-2)+q+(n-2)+5 := by
    exact_mod_cast hparent
  have hpow : 8*(2:Int)^(n-2)=(2:Int)^(n+1) := by
    have he : n+1=(n-2)+3 := by omega
    rw [he,Int.pow_add]
    norm_num
    ring
  have h8d : 8*(d:Int)=
      (2:Int)^(n+2)+2*q+2*n+6 := by
    calc
      8*(d:Int)=2*(4*(d:Int)) := by ring
      _=2*(8*(2:Int)^(n-2)+q+(n-2)+5) := by rw [hparentI]
      _=2*((2:Int)^(n+1)+q+n+3) := by rw [hpow]; omega
      _=(2:Int)^(n+2)+2*q+2*n+6 := by
        rw [show (2:Int)^(n+2)=(2:Int)^(n+1)*2 by
          rw [Int.pow_succ]]
        ring
  dsimp [qNumerator]
  rw [hz]
  calc
    8*(9*(d:Int))-9*((2:Int)^(n+2)+2*n+1) =
        9*(8*(d:Int)-((2:Int)^(n+2)+2*n+1)) := by ring
    _=9*(2*q+5) := by rw [h8d]; ring

#print axioms qNumerator_shift_digit_mod
#print axioms qNumerator_lift_criterion
#print axioms qNumerator_unique_lift
#print axioms qIndexResidue_good
#print axioms qIndexResidue_iff
#print axioms qIndexResidue_all_sectors_iff
#print axioms qIndexResidue_887_iff
#print axioms qNumerator_t1_parent_identity

end CascadeQStateIndexHensel
