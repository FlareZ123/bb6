import RayDepthHensel
set_option maxHeartbeats 0

namespace CascadeRayDepthResidue
open CascadeRayDepthHensel CascadeRayPeriod

/-- A computable residue lift, one ternary digit per precision. -/
def depthResidue (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let b := depthResidue n k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := signedZ n b/(3:Int)^(k+1)
      b + henselDigit q a * depthPeriod k

private theorem depthPeriod_pos (k : Nat) : 0 < depthPeriod k := by
  change 0 < 2*3^k
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

private theorem depthPeriod_next (k : Nat) :
    depthPeriod (k+1) = 3*depthPeriod k := by
  simp only [depthPeriod,Nat.pow_succ]
  omega

private theorem depthResidue_lt (n k : Nat) :
    depthResidue n k < depthPeriod k := by
  induction k with
  | zero =>
      simp [depthResidue, depthPeriod]
  | succ k ih =>
      let b := depthResidue n k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := signedZ n b/(3:Int)^(k+1)
      let d := henselDigit q a
      have hd : d < 3 := henselDigit_lt q a
      have hmul := Nat.mul_le_mul_right (depthPeriod k) (show d ≤ 2 by omega)
      have hnext := depthPeriod_next k
      have hdef : depthResidue n (k+1) = b+d*depthPeriod k := rfl
      rw [hdef,hnext]
      omega

private theorem depthResidue_good (n k : Nat) (hn:n%6=4 ∨ n%6=5) :
    (3:Int)^(k+1) ∣ signedZ n (depthResidue n k) := by
  induction k with
  | zero =>
      have h := (signedZ_mod_three_even_iff n 0 hn).mpr (by decide)
      simpa [depthResidue, Int.dvd_iff_emod_eq_zero] using h
  | succ k ih =>
      let b := depthResidue n k
      let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := signedZ n b/(3:Int)^(k+1)
      let d := henselDigit q a
      have ha : a % 3 ≠ 0 := by
        simpa [a] using rayCoeff_unit n b k hn
      have hd : d < 3 := henselDigit_lt q a
      have hdiv : (3:Int) ∣ q-a*d := by
        simpa [d] using henselDigit_divides q a ha
      have hbase : (3:Int)^(k+1) ∣ signedZ n b := ih
      have hlift := (signedZ_lift_criterion n b k d hd hbase).mpr
        (by simpa [q,a] using hdiv)
      simpa [depthResidue,b,a,q,d] using hlift

private theorem period_dvd_iff (n j k m : Nat) :
    ((3:Int)^(k+1) ∣ signedZ n (j+m*depthPeriod k)) ↔
    ((3:Int)^(k+1) ∣ signedZ n j) := by
  simp only [Int.dvd_iff_emod_eq_zero]
  rw [signedZ_period_mul]

private theorem period_mod_dvd_iff (n j k : Nat) :
    ((3:Int)^(k+1) ∣ signedZ n j) ↔
    ((3:Int)^(k+1) ∣ signedZ n (j%depthPeriod k)) := by
  have h := period_dvd_iff n (j%depthPeriod k) k (j/depthPeriod k)
  have he : j%depthPeriod k+(j/depthPeriod k)*depthPeriod k=j :=
    Nat.mod_add_div' j (depthPeriod k)
  rw [he] at h
  exact h

private theorem small_digit_unique (n k : Nat) (hn:n%6=4 ∨ n%6=5)
    (t : Nat) (ht:t<3) :
    ((3:Int)^(k+2) ∣ signedZ n
      (depthResidue n k+t*depthPeriod k)) ↔
    t = henselDigit
      (signedZ n (depthResidue n k)/(3:Int)^(k+1))
      ((2*n+3:Int)*(2:Int)^(depthResidue n k+1)*depthCoeff k) := by
  let b := depthResidue n k
  let a : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  let q : Int := signedZ n b/(3:Int)^(k+1)
  have ha : a%3 ≠ 0 := by simpa [a] using rayCoeff_unit n b k hn
  have hbase := depthResidue_good n k hn
  have hc := signedZ_lift_criterion n b k t ht hbase
  constructor
  · intro hh
    have hd : (3:Int) ∣ q-a*t := by
      exact hc.mp hh
    exact henselDigit_div q a ha t ht hd
  · intro ht'
    subst t
    apply hc.mpr
    exact henselDigit_divides q a ha

/-- An exact single depth class at every 3-adic precision, for all natural depths. -/
theorem depthResidue_iff (n k j : Nat) (hn : n%6=4 ∨ n%6=5) :
    ((3:Int)^(k+1) ∣ signedZ n j) ↔
      j % depthPeriod k = depthResidue n k := by
  induction k generalizing j with
  | zero =>
      have h := signedZ_mod_three_even_iff n j hn
      simpa [depthPeriod,depthResidue,Int.dvd_iff_emod_eq_zero] using h
  | succ k ih =>
      let p := depthPeriod k
      let pn := depthPeriod (k+1)
      let b := depthResidue n k
      let d := henselDigit
        (signedZ n b/(3:Int)^(k+1))
        ((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)
      have hstep : pn = 3*p := depthPeriod_next k
      have hdiv : (3:Int)^(k+1) ∣ (3:Int)^(k+2) := by
        refine ⟨3, ?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz : (3:Int)^(k+2) ∣ signedZ n (j%pn) :=
          (period_mod_dvd_iff n j (k+1)).mp hx
        have hlo : (3:Int)^(k+1) ∣ signedZ n (j%pn) := by
          cases hz with
          | intro w hw =>
            cases hdiv with
            | intro v hv =>
              refine ⟨v*w, ?_⟩
              rw [hw,hv]
              ac_rfl
        have hb : (j%pn)%p=b := (ih (j%pn)).mp hlo
        have hp : 0<p := depthPeriod_pos k
        have hjlt : j%pn <3*p := by
          have h := Nat.mod_lt j (depthPeriod_pos (k+1))
          simpa only [pn,hstep] using h
        have ht : (j%pn)/p<3 := by
          apply (Nat.div_lt_iff_lt_mul hp).mpr
          exact hjlt
        have heq : j%pn = b + ((j%pn)/p)*p := by
          have hh := Nat.mod_add_div' (j%pn) p
          omega
        have hd' := (small_digit_unique n k hn ((j%pn)/p) ht).mp
          (by rw [←heq]; exact hz)
        have hnext : depthResidue n (k+1)=b+d*p := rfl
        have hdnum : (j%pn)/p=d := by simpa only [b,d] using hd'
        have htarget : j%pn=b+d*p := by rw [←hdnum]; exact heq
        change j%pn = depthResidue n (k+1)
        rw [hnext]
        exact htarget
      · intro hx
        apply (period_mod_dvd_iff n j (k+1)).mpr
        rw [hx]
        exact depthResidue_good n (k+1) hn

#print axioms depthResidue_iff
#print axioms depthResidue_good
end CascadeRayDepthResidue
