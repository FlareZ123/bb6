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
def tThreeHighC (n : Nat) : Nat := (38*(2^(n+1)+2*n-1))%81

def tThreeHighOffset (n : Nat) : Int := (81:Int)*(tThreeHighC n:Int)

def tThreeHighResidue (n : Nat) : Nat := translatedDepthResidue n (tThreeHighOffset n) 4

theorem tThreeHighOffset_divisible (n : Nat) : (3:Int)^4∣tThreeHighOffset n := by
  have hp : (3:Int)^4=81 := by decide
  rw [hp,tThreeHighOffset]
  exact Int.dvd_mul_right 81 (tThreeHighC n:Int)

/-- The high-q t=3 gate occupies exactly one ray-depth class modulo 4374. -/
theorem tThreeHighResidue_iff (n j : Nat) (hn : n%6=4 ∨ n%6=5) :
    (3:Int)^8∣signedZ n j-tThreeHighOffset n ↔
      j%4374=tThreeHighResidue n := by
  have h := translatedDepthResidue_iff n (tThreeHighOffset n) 4 j hn
    (tThreeHighOffset_divisible n)
  have hp : depthPeriod 7=4374 := by decide
  simpa [translatedZ, tThreeHighResidue, hp] using h

#print axioms translatedZ_lift_criterion
#print axioms translatedDepthResidue_good
#print axioms translatedDepthResidue_iff
#print axioms translatedDepthResidue_unique_in_period
#print axioms tThreeHighResidue_iff
end CascadeTranslatedRayDepth
