import RayDepthResidue
set_option maxHeartbeats 0
namespace CascadeTranslatedRayDepth
open CascadeRayPeriod CascadeRayDepthHensel CascadeRayDepthResidue

def translatedZ (n : Nat) (offset : Int) (j : Nat) : Int :=
  signedZ n j - offset

theorem translatedZ_lift_criterion (n b k t : Nat) (offset : Int) (ht : t < 3)
    (hbase : (3:Int)^(k+1) ∣ translatedZ n offset b) :
    (3:Int)^(k+2) ∣ translatedZ n offset (b+t*depthPeriod k) ↔
      (3:Int) ∣ (translatedZ n offset b/(3:Int)^(k+1) -
        ((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)*t) := by
  let m : Int := (3:Int)^(k+1)
  let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  have hmne : m ≠ 0 := by
    change (3:Int)^(k+1) ≠ 0
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < (3:Nat))))
  have hM : (3:Int)^(k+2) = (3:Int)*m := by
    dsimp [m]
    rw [show k+2=(k+1)+1 by omega, Int.pow_succ]
    exact Int.mul_comm _ _
  have hmod := signedZ_shift_digit_mod n b k t ht
  have hmod' :
      translatedZ n offset (b+t*depthPeriod k)%(3:Int)^(k+2) =
        (translatedZ n offset b-m*(a*t))%(3:Int)^(k+2) := by
    dsimp [translatedZ]
    apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
    have hdiff := (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 hmod
    let z : Int := m*(a*t)
    have hz : z = (t:Int)*(depthCoeff k:Int)*((2*n+3:Int)*(2:Int)^(b+1)*m) := by
      dsimp [z,a,m]
      ac_rfl
    have heq :
        (signedZ n (b+t*depthPeriod k)-offset)-
          ((signedZ n b-offset)-z) =
        signedZ n (b+t*depthPeriod k)-(signedZ n b-z) := by
      dsimp [z]
      omega
    rw [heq]
    simpa [hz, m, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using hdiff
  have hdiviff :
      (3:Int)^(k+2) ∣ translatedZ n offset (b+t*depthPeriod k) ↔
      (3:Int)^(k+2) ∣ translatedZ n offset b-m*(a*t) := by
    rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, hmod']
  have hquot : m*(translatedZ n offset b/m)=translatedZ n offset b :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor : translatedZ n offset b-m*(a*t) =
      m*(translatedZ n offset b/m-a*t) := by
    calc
      _ = m*(translatedZ n offset b/m)-m*(a*t) := by rw [hquot]
      _ = m*(translatedZ n offset b/m-a*t) := by rw [Int.mul_sub]
  rw [hdiviff,hfactor,hM]
  have hcomm : (3:Int)*m=m*3 := Int.mul_comm _ _
  rw [hcomm]
  exact Int.mul_dvd_mul_iff_left hmne

/-- Lift a translated target from the canonical zero-divisibility class at precision 3^4. -/
def translatedDepthResidue (n : Nat) (offset : Int) : Nat → Nat
  | 0 => depthResidue n 3
  | k+1 =>
      let b := translatedDepthResidue n offset k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff (k+3)
      let q : Int := translatedZ n offset b/(3:Int)^(k+4)
      b+henselDigit q a*depthPeriod (k+3)

theorem translatedDepthResidue_lt (n : Nat) (offset : Int) (k : Nat) :
    translatedDepthResidue n offset k < depthPeriod (k+3) := by
  induction k with
  | zero =>
      simpa [translatedDepthResidue] using depthResidue_lt n 3
  | succ k ih =>
      let b := translatedDepthResidue n offset k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff (k+3)
      let q : Int := translatedZ n offset b/(3:Int)^(k+4)
      let d := henselDigit q a
      have hd : d<3 := henselDigit_lt q a
      have hp : 0<depthPeriod (k+3) := by
        change 0 < 2*3^(k+3)
        exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      have hnext : depthPeriod (k+4)=3*depthPeriod (k+3) := by
        simp [depthPeriod,Nat.pow_succ]
        omega
      have hdef : translatedDepthResidue n offset (k+1)=b+d*depthPeriod (k+3) := rfl
      have hmul : d*depthPeriod (k+3) ≤ 2*depthPeriod (k+3) :=
        Nat.mul_le_mul_right (depthPeriod (k+3)) (by omega)
      rw [hdef,hnext]
      omega

private theorem translatedZ_base_equiv (n : Nat) (offset : Int) (j : Nat)
    (hoff : (3:Int)^4 ∣ offset) :
    (3:Int)^4 ∣ translatedZ n offset j ↔ (3:Int)^4 ∣ signedZ n j := by
  constructor
  · intro h
    have h' := Int.dvd_add h hoff
    simpa [translatedZ] using h'
  · intro h
    exact Int.dvd_sub h hoff

theorem translatedDepthResidue_good (n : Nat) (offset : Int) (k : Nat)
    (hn : n%6=4 ∨ n%6=5) (hoff : (3:Int)^4 ∣ offset) :
    (3:Int)^(k+4) ∣ translatedZ n offset (translatedDepthResidue n offset k) := by
  induction k with
  | zero =>
      have hlt := depthResidue_lt n 3
      have hbase : (3:Int)^4 ∣ signedZ n (depthResidue n 3) := by
        exact (depthResidue_iff n 3 (depthResidue n 3) hn).2
          (by simpa [Nat.mod_eq_of_lt hlt])
      have h := Int.dvd_sub hbase hoff
      simpa [translatedDepthResidue,translatedZ] using h
  | succ k ih =>
      let b := translatedDepthResidue n offset k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff (k+3)
      let q : Int := translatedZ n offset b/(3:Int)^(k+4)
      let d := henselDigit q a
      have ha : a%3≠0 := by simpa [a] using rayCoeff_unit n b (k+3) hn
      have hd : d<3 := henselDigit_lt q a
      have hdiv : (3:Int)∣q-a*d := by
        simpa [d,q,a] using henselDigit_divides q a ha
      have hcrit := translatedZ_lift_criterion n b (k+3) d offset hd ih
      have hgood : (3:Int)^(k+5) ∣
          translatedZ n offset (b+d*depthPeriod (k+3)) :=
        hcrit.mpr (by simpa [q,a] using hdiv)
      simpa [translatedDepthResidue,b,a,q,d] using hgood

theorem translatedZ_period (n : Nat) (offset : Int) (j k : Nat) :
    translatedZ n offset (j+depthPeriod k)%(3:Int)^(k+1) =
      translatedZ n offset j%(3:Int)^(k+1) := by
  change (signedZ n (j+depthPeriod k)-offset)%(3:Int)^(k+1) =
    (signedZ n j-offset)%(3:Int)^(k+1)
  calc
    _ = ((signedZ n (j+depthPeriod k)%(3:Int)^(k+1)) -
        offset%(3:Int)^(k+1))%(3:Int)^(k+1) := by rw [Int.sub_emod]
    _ = ((signedZ n j%(3:Int)^(k+1)) -
        offset%(3:Int)^(k+1))%(3:Int)^(k+1) := by rw [signedZ_period]
    _ = _ := (Int.sub_emod _ _ _).symm

theorem translatedZ_period_mul (n : Nat) (offset : Int) (j k m : Nat) :
    translatedZ n offset (j+m*depthPeriod k)%(3:Int)^(k+1) =
      translatedZ n offset j%(3:Int)^(k+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx : j+(m+1)*depthPeriod k=(j+m*depthPeriod k)+depthPeriod k := by
        rw [Nat.succ_mul]
        omega
      rw [hidx,translatedZ_period]
      exact ih

private theorem translated_period_mod_dvd_iff (n : Nat) (offset : Int)
    (j k : Nat) :
    (3:Int)^(k+1)∣translatedZ n offset j ↔
      (3:Int)^(k+1)∣translatedZ n offset (j%depthPeriod k) := by
  rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero]
  have h := translatedZ_period_mul n offset (j%depthPeriod k) k (j/depthPeriod k)
  have he : j%depthPeriod k+(j/depthPeriod k)*depthPeriod k=j :=
    Nat.mod_add_div' j (depthPeriod k)
  rw [he] at h
  constructor
  · intro hx
    rw [←h]
    exact hx
  · intro hy
    rw [h]
    exact hy

private theorem pow_three_dvd_next (k : Nat) :
    (3:Int)^(k+4)∣(3:Int)^(k+5) := by
  refine ⟨3,?_⟩
  rw [show k+5=(k+4)+1 by omega,Int.pow_succ]

/-- The translated target has exactly one residue class modulo the depth period at every precision. -/
theorem translatedDepthResidue_iff (n : Nat) (offset : Int) (k j : Nat)
    (hn : n%6=4 ∨ n%6=5) (hoff : (3:Int)^4∣offset) :
    (3:Int)^(k+4)∣translatedZ n offset j ↔
      j%depthPeriod (k+3)=translatedDepthResidue n offset k := by
  induction k generalizing j with
  | zero =>
      change (3:Int)^4∣translatedZ n offset j ↔
        j%depthPeriod 3=depthResidue n 3
      exact (translatedZ_base_equiv n offset j hoff).trans (depthResidue_iff n 3 j hn)
  | succ k ih =>
      let p := depthPeriod (k+3)
      let pn := depthPeriod (k+4)
      let b := translatedDepthResidue n offset k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff (k+3)
      let q : Int := translatedZ n offset b/(3:Int)^(k+4)
      let d := henselDigit q a
      have hstep : pn=3*p := by
        simp [pn,p,depthPeriod,Nat.pow_succ]
        omega
      have hp : 0<p := by
        change 0 < 2*3^(k+3)
        exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      constructor
      · intro hhigh
        have hhigh0 := (translated_period_mod_dvd_iff n offset j (k+4)).mp hhigh
        have hlow0 : (3:Int)^(k+4)∣translatedZ n offset (j%pn) :=
          Int.dvd_trans (pow_three_dvd_next k) hhigh0
        have hb : (j%pn)%p=b := (ih (j%pn)).mp hlow0
        have hjlt : j%pn<3*p := by
          rw [←hstep]
          exact Nat.mod_lt j (by
            have : 0<pn := by
              change 0 < 2*3^(k+4)
              exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
            exact this)
        have ht : (j%pn)/p<3 :=
          (Nat.div_lt_iff_lt_mul hp).2 hjlt
        have hsplit : j%pn=b+(j%pn)/p*p := by
          have hh := Nat.mod_add_div' (j%pn) p
          rw [hb] at hh
          exact hh.symm
        have hcrit := translatedZ_lift_criterion n b (k+3) (j%pn/p) offset ht
          (translatedDepthResidue_good n offset k hn hoff)
        have hdiv : (3:Int)∣q-a*(j%pn/p) := by
          rw [hsplit] at hhigh0
          exact hcrit.mp hhigh0
        have htd : j%pn/p=d := by
          exact henselDigit_div q a (by simpa [a] using rayCoeff_unit n b (k+3) hn)
            (j%pn/p) ht (by simpa [q,a] using hdiv)
        have hnext : translatedDepthResidue n offset (k+1)=b+d*p := rfl
        have hsplit' := hsplit
        rw [htd] at hsplit'
        change j%pn=translatedDepthResidue n offset (k+1)
        rw [hnext]
        exact hsplit'
      · intro hres
        apply (translated_period_mod_dvd_iff n offset j (k+4)).mpr
        rw [hres]
        exact translatedDepthResidue_good n offset (k+1) hn hoff

theorem translatedDepthResidue_unique_in_period (n : Nat) (offset : Int)
    (k j : Nat) (hn : n%6=4 ∨ n%6=5) (hoff : (3:Int)^4∣offset)
    (hj : j<depthPeriod (k+3)) :
    (3:Int)^(k+4)∣translatedZ n offset j ↔ j=translatedDepthResidue n offset k := by
  rw [translatedDepthResidue_iff n offset k j hn hoff]
  simp only [Nat.mod_eq_of_lt hj]

/-- Quotient offset selected by the source t=3 high-q gate. -/
def tThreeHighC (n : Nat) : Int := (38*((2:Int)^(n+1)+2*n-1))%81

def tThreeHighOffset (n : Nat) : Int := (81:Int)*tThreeHighC n

def tThreeHighResidue (n : Nat) : Nat := translatedDepthResidue n (tThreeHighOffset n) 4

theorem tThreeHighOffset_divisible (n : Nat) : (3:Int)^4∣tThreeHighOffset n := by
  have hp : (3:Int)^4=81 := by decide
  rw [hp,tThreeHighOffset]
  exact Int.dvd_mul_right 81 (tThreeHighC n)

/-- The high-q t=3 gate occupies exactly one ray-depth class modulo 4374. -/
theorem tThreeHighResidue_iff (n j : Nat) (hn : n%6=4 ∨ n%6=5) :
    (3:Int)^8∣signedZ n j-tThreeHighOffset n ↔
      j%4374=tThreeHighResidue n := by
  have h := translatedDepthResidue_iff n (tThreeHighOffset n) 4 j hn
    (tThreeHighOffset_divisible n)
  have hp : depthPeriod 7=4374 := by decide
  simpa [translatedZ, tThreeHighResidue, hp] using h

/-- The quotient gate is exactly the translated 3^8 divisibility condition. -/
theorem tThreeHighGate_iff (n j d q : Nat)
    (hz : signedZ n j=(81:Int)*d)
    (hrel : 16*d=2^n+q+n+2) :
    (81:Int)∣(2*q+5:Int) ↔
      (3:Int)^8∣signedZ n j-tThreeHighOffset n := by
  have hrelI : (16:Int)*(d:Int)=(2:Int)^n+q+n+2 := by
    exact_mod_cast hrel
  have hpow : (2:Int)^(n+1)=2*(2:Int)^n := by
    rw [Int.pow_succ]
    exact Int.mul_comm _ _
  have h32 : (32:Int)*(d:Int)=(2:Int)^(n+1)+2*q+2*n+4 := by
    have hh := congrArg (fun x:Int => 2*x) hrelI
    omega
  have hqexpr : (2:Int)*q+5=
      (32:Int)*d-((2:Int)^(n+1)+2*n-1) := by omega
  let X : Int := (2:Int)^(n+1)+2*n-1
  let c : Int := tThreeHighC n
  have hc : c=(38*X)%81 := by rfl
  have hdivc : (81:Int)∣(32:Int)*c-X := by
    have hh := hc
    omega
  have hsplit : (32:Int)*d-X=(32:Int)*(d-c)+((32:Int)*c-X) := by omega
  have hA : (81:Int)∣(32:Int)*d-X ↔ (81:Int)∣(32:Int)*(d-c) := by
    rw [hsplit]
    exact Int.dvd_add_left hdivc
  have hcancel : (81:Int)∣(32:Int)*(d-c) ↔ (81:Int)∣d-c := by
    constructor
    · intro hh
      have hmul : (81:Int)∣(38:Int)*((32:Int)*(d-c)) :=
        Int.dvd_mul_of_dvd_right hh
      have heq : (38:Int)*((32:Int)*(d-c))=(d-c)+81*(15*(d-c)) := by
        omega
      have h' : (81:Int)∣(d-c)+81*(15*(d-c)) := by simpa [heq] using hmul
      exact (Int.dvd_add_left (Int.dvd_mul_right 81 (15*(d-c)))).1 h'
    · intro hh
      exact Int.dvd_mul_of_dvd_right hh
  have hshift : signedZ n j-tThreeHighOffset n=(81:Int)*(d-c) := by
    rw [hz,tThreeHighOffset]
    omega
  have hfinal : (3:Int)^8∣signedZ n j-tThreeHighOffset n ↔
      (81:Int)∣d-c := by
    rw [show (3:Int)^8=(81:Int)*81 by decide,hshift]
    exact Int.mul_dvd_mul_iff_left (by decide : (81:Int)≠0)
  calc
    (81:Int)∣(2*q+5:Int) ↔ (81:Int)∣(32:Int)*d-X := by
      rw [hqexpr]
    _ ↔ (81:Int)∣d-c := hA.trans hcancel
    _ ↔ (3:Int)^8∣signedZ n j-tThreeHighOffset n := hfinal.symm

theorem tThreeHighC_bounds (n : Nat) :
    0≤tThreeHighC n ∧ tThreeHighC n<81 := by
  constructor
  · exact Int.emod_nonneg _ (by decide)
  · exact Int.emod_lt_of_pos _ (by decide)

/-- Source t=3 high-q gate, expressed as its unique depth residue modulo 4374. -/
theorem tThreeHighGate_residue_iff (n j d q : Nat)
    (hn : n%6=4 ∨ n%6=5)
    (hz : signedZ n j=(81:Int)*d)
    (hrel : 16*d=2^n+q+n+2) :
    (81:Int)∣(2*q+5:Int) ↔ j%4374=tThreeHighResidue n := by
  exact (tThreeHighGate_iff n j d q hz hrel).trans (tThreeHighResidue_iff n j hn)

private theorem two_pow_mod_three (k : Nat) :
    2^k%3=(if k%2=0 then 1 else 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ,Nat.mul_mod,ih]
      by_cases h:k%2=0
      · simp[h]; omega
      · have hk:k%2=1:=by omega
        simp[hk]; omega

theorem tThreeHighCenter_divisible (n : Nat) :
    (81:Int)∣(32:Int)*tThreeHighC n-((2:Int)^(n+1)+2*n-1) := by
  let X : Int := (2:Int)^(n+1)+2*n-1
  have hc : tThreeHighC n=(38*X)%81 := by rfl
  have hcrem : tThreeHighC n%81=(38*X)%81 := by
    rw [hc,Int.emod_emod]
  have hmul : (32:Int)*38=1+15*81 := by decide
  have hrem : ((38:Int)*X%81-(38:Int)*X)%81=0 := by
    have h : ((38:Int)*X%81)%81=((38:Int)*X)%81 := by rw [Int.emod_emod]
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h
  have hprod : ((32:Int)*((38:Int)*X%81)-(32:Int)*((38:Int)*X))%81=0 := by
    rw [←Int.mul_sub,Int.mul_emod,hrem]
    simp
  have hconst : ((1:Int)+15*81)%81=1 := by omega
  have h32 : (32:Int)*tThreeHighC n%81=X%81 := by
    calc
      (32:Int)*tThreeHighC n%81=((32:Int)%81*(tThreeHighC n%81))%81 := by rw [Int.mul_emod]
      _=(32:Int)*((38*X)%81)%81 := by simp [hcrem]
      _=(32:Int)*(38*X)%81 := by exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).2 hprod
      _=X%81 := by
        rw [←Int.mul_assoc,hmul,Int.mul_emod,hconst]
        simp
  rw [Int.dvd_iff_emod_eq_zero,Int.sub_emod,h32]
  dsimp [X]
  simp

def tThreeHighK (n : Nat) : Int :=
  ((32:Int)*tThreeHighC n-((2:Int)^(n+1)+2*n-1))/81

theorem tThreeHighK_exact (n : Nat) :
    (81:Int)*tThreeHighK n=
      (32:Int)*tThreeHighC n-((2:Int)^(n+1)+2*n-1) := by
  exact Int.mul_ediv_cancel_of_dvd (tThreeHighCenter_divisible n)

def tThreeHighRZeroOffset (n : Nat) : Int :=
  tThreeHighOffset n+(6561:Int)*(tThreeHighK n+1)

def tThreeHighRZeroResidue (n : Nat) : Nat :=
  translatedDepthResidue n (tThreeHighRZeroOffset n) 5

theorem tThreeHighRZeroOffset_divisible (n : Nat) :
    (3:Int)^4∣tThreeHighRZeroOffset n := by
  have hp : (3:Int)^4=81 := by decide
  rw [hp,tThreeHighRZeroOffset,tThreeHighOffset]
  apply Int.dvd_add
  · exact Int.dvd_mul_right 81 (tThreeHighC n)
  · rw [show (6561:Int)=(81:Int)*81 by decide,Int.mul_assoc]
    exact Int.dvd_mul_right 81 (81*(tThreeHighK n+1))

/-- The r mod 3 zero branch is a unique translated ray-depth class modulo 13122. -/
theorem tThreeHighRZeroResidue_iff (n j : Nat) (hn : n%6=4 ∨ n%6=5) :
    (3:Int)^9∣signedZ n j-tThreeHighRZeroOffset n ↔
      j%13122=tThreeHighRZeroResidue n := by
  have h := translatedDepthResidue_iff n (tThreeHighRZeroOffset n) 5 j hn
    (tThreeHighRZeroOffset_divisible n)
  have hp : depthPeriod 8=13122 := by decide
  simpa [translatedZ,tThreeHighRZeroResidue,hp] using h

/-- The second t=3 parent has residue zero exactly on the precision-nine lift. -/
theorem tThreeHighSecondParent_mod_zero_iff (n j d q e r : Nat)
    (hn : 20≤n) (hsector : n%6=4 ∨ n%6=5)
    (hz : signedZ n j=(81:Int)*d)
    (hrel : 16*d=2^n+q+n+2)
    (hgate : 2*q+5=81*e)
    (hrrel : 16*e=8*2^(n-6)+r+(n-6)+5) :
    r%3=0 ↔ (3:Int)^9∣signedZ n j-tThreeHighRZeroOffset n := by
  have hgateI : (81:Int)∣(2*q+5:Int) := by
    refine ⟨(e:Int),?_⟩
    exact_mod_cast hgate
  have htranslated : (3:Int)^8∣signedZ n j-tThreeHighOffset n :=
    (tThreeHighGate_iff n j d q hz hrel).mp hgateI
  have hshift : signedZ n j-tThreeHighOffset n=
      (81:Int)*((d:Int)-tThreeHighC n) := by
    rw [hz,tThreeHighOffset]
    omega
  have hdivdc : (81:Int)∣(d:Int)-tThreeHighC n := by
    have hp : (3:Int)^8=(81:Int)*81 := by decide
    rw [hp,hshift] at htranslated
    exact (Int.mul_dvd_mul_iff_left (by decide : (81:Int)≠0)).mp htranslated
  obtain ⟨s,hs⟩ := hdivdc
  have hd : (d:Int)=tThreeHighC n+81*s := by omega
  have hqexpr : (2:Int)*q+5=
      (32:Int)*d-((2:Int)^(n+1)+2*n-1) := by
    have hrelI : (16:Int)*(d:Int)=(2:Int)^n+q+n+2 := by exact_mod_cast hrel
    have hpow : (2:Int)^(n+1)=2*(2:Int)^n := by
      rw [Int.pow_succ]
      exact Int.mul_comm _ _
    have h32 : (32:Int)*(d:Int)=(2:Int)^(n+1)+2*q+2*n+4 := by
      have hh:=congrArg (fun x:Int=>2*x) hrelI
      omega
    omega
  have hK : (81:Int)*tThreeHighK n=
      (32:Int)*tThreeHighC n-((2:Int)^(n+1)+2*n-1) :=
    tThreeHighK_exact n
  have heq : (e:Int)=tThreeHighK n+32*s := by
    have heq0 : (81:Int)*(e:Int)=
        (81:Int)*(tThreeHighK n+32*s) := by
      calc
        (81:Int)*(e:Int)=(2:Int)*q+5 := by exact_mod_cast hgate.symm
        _=(32:Int)*(d:Int)-((2:Int)^(n+1)+2*n-1) := hqexpr
        _=(81:Int)*(tThreeHighK n+32*s) := by
          rw [hd]
          omega
    omega
  have hpowNat : 8*2^(n-6)=2^(n-3) := by
    calc
      8*2^(n-6)=2^3*2^(n-6) := by congr 1 <;> decide
      _=2^((n-6)+3) := by
        rw [Nat.pow_add]
        exact Nat.mul_comm _ _
      _=2^(n-3) := by congr 1; omega
  have hrrel' : 16*e+1=2^(n-3)+r+n := by
    rw [hpowNat] at hrrel
    omega
  have hrrelI : (16:Int)*(e:Int)+1=(2:Int)^(n-3)+r+n := by
    exact_mod_cast hrrel'
  have hrformulaI : (r:Int)=16*e-(2:Int)^(n-3)-n+1 := by omega
  have hconst : (2^(n-3)+n)%3=0 := by
    have hpow := two_pow_mod_three (n-3)
    rcases hsector with h|h
    · have hneq : (n-3)%2≠0 := by omega
      rw [if_neg hneq] at hpow
      omega
    · have hpar : (n-3)%2=0 := by omega
      rw [if_pos hpar] at hpow
      omega
  have hconstI : ((2:Int)^(n-3)+n)%3=0 := by exact_mod_cast hconst
  have hrmodI : (r:Int)%3=((e:Int)+1)%3 := by omega
  have hresI : ((e:Int)+1)%3=0 ↔
      (s-(tThreeHighK n+1))%3=0 := by omega
  have hrzeroI : (r:Int)%3=0 ↔ (s-(tThreeHighK n+1))%3=0 := by
    rw [hrmodI]
    exact hresI
  have hrzero : r%3=0 ↔ (s-(tThreeHighK n+1))%3=0 := by
    exact_mod_cast hrzeroI
  have hshiftR : signedZ n j-tThreeHighRZeroOffset n=
      (6561:Int)*(s-(tThreeHighK n+1)) := by
    rw [hz,tThreeHighRZeroOffset,tThreeHighOffset]
    omega
  have hdivR : (3:Int)^9∣signedZ n j-tThreeHighRZeroOffset n ↔
      (3:Int)∣s-(tThreeHighK n+1) := by
    rw [show (3:Int)^9=(6561:Int)*3 by decide,hshiftR]
    exact Int.mul_dvd_mul_iff_left (by decide : (6561:Int)≠0)
  have hmodR : (3:Int)∣s-(tThreeHighK n+1) ↔
      (s-(tThreeHighK n+1))%3=0 := Int.dvd_iff_emod_eq_zero
  rw [hrzero]
  exact (hdivR.trans hmodR).symm

#print axioms translatedZ_lift_criterion
#print axioms translatedDepthResidue_good
#print axioms translatedDepthResidue_iff
#print axioms translatedDepthResidue_unique_in_period
#print axioms tThreeHighResidue_iff
#print axioms tThreeHighGate_iff
#print axioms tThreeHighC_bounds
#print axioms tThreeHighGate_residue_iff
#print axioms tThreeHighRZeroResidue_iff
#print axioms tThreeHighSecondParent_mod_zero_iff
end CascadeTranslatedRayDepth
