import QDepthBase
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

theorem qDepthResidue_lt (n k : Nat) :
    qDepthResidue n k<depthPeriod k := by
  induction k with
  | zero => simp [qDepthResidue,depthPeriod]
  | succ k ih =>
      let b:=qDepthResidue n k
      let a : Int := 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := qNumerator n b/(3:Int)^(k+1)
      let d:=henselDigit q a
      have hd:d<3:=henselDigit_lt q a
      have hmul:=Nat.mul_le_mul_right (depthPeriod k) (show d≤2 by omega)
      have hnext:=depthPeriod_next k
      have hdef:qDepthResidue n (k+1)=b+d*depthPeriod k:=rfl
      rw [hdef,hnext]
      omega

theorem qDepthResidue_good (n k : Nat)
    (hn:n%6=4 ∨ n%6=5) :
    (3:Int)^(k+1)∣qNumerator n (qDepthResidue n k) := by
  induction k with
  | zero =>
      have h := (q_mod_three_even_iff n 0 hn).mpr (by decide)
      simpa [qDepthResidue,Int.dvd_iff_emod_eq_zero] using h
  | succ k ih =>
      let b:=qDepthResidue n k
      let a : Int := 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := qNumerator n b/(3:Int)^(k+1)
      let d:=henselDigit q a
      have ha:a%3≠0:=by simpa [a] using qCoeff_unit n b k hn
      have hd:d<3:=henselDigit_lt q a
      have hdiv:(3:Int)∣q-a*d:=by simpa [d] using henselDigit_divides q a ha
      have hbase:(3:Int)^(k+1)∣qNumerator n b:=ih
      have hlift:=(q_lift_criterion n b k d hd hbase).mpr (by simpa [q,a] using hdiv)
      simpa [qDepthResidue,b,a,q,d] using hlift

theorem q_period_dvd_iff (n j k m : Nat) :
    ((3:Int)^(k+1)∣qNumerator n (j+m*depthPeriod k)) ↔
      ((3:Int)^(k+1)∣qNumerator n j) := by
  have hs := signedZ_period_mul n j k m
  have hsdvd :
      (3:Int)^(k+1)∣signedZ n (j+m*depthPeriod k)-signedZ n j := by
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 hs
  have hqdiff :
      qNumerator n (j+m*depthPeriod k)-qNumerator n j =
        8*(signedZ n (j+m*depthPeriod k)-signedZ n j) := by
    dsimp [qNumerator]
    rw [Int.mul_sub]
    omega
  have hqdiv :
      (3:Int)^(k+1)∣qNumerator n (j+m*depthPeriod k)-qNumerator n j := by
    rcases hsdvd with ⟨w,hw⟩
    refine ⟨8*w,?_⟩
    rw [hqdiff,hw]
    ac_rfl
  constructor
  · intro h
    have h' : (3:Int)^(k+1) ∣
        8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1) := by
      simpa [qNumerator] using h
    have hqdiv' : (3:Int)^(k+1) ∣
        (8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1))-
          (8*signedZ n j-9*((2:Int)^(n+2)+2*n+1)) := by
      simpa [qNumerator] using hqdiv
    have hh := Int.dvd_sub h' hqdiv'
    have heq :
        (8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1))-
          ((8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1))-
            (8*signedZ n j-9*((2:Int)^(n+2)+2*n+1))) =
          8*signedZ n j-9*((2:Int)^(n+2)+2*n+1) := by omega
    rw [heq] at hh
    simpa [qNumerator] using hh
  · intro h
    have h' : (3:Int)^(k+1) ∣
        8*signedZ n j-9*((2:Int)^(n+2)+2*n+1) := by
      simpa [qNumerator] using h
    have hqdiv' : (3:Int)^(k+1) ∣
        (8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1))-
          (8*signedZ n j-9*((2:Int)^(n+2)+2*n+1)) := by
      simpa [qNumerator] using hqdiv
    have hh := Int.dvd_add h' hqdiv'
    have heq :
        (8*signedZ n j-9*((2:Int)^(n+2)+2*n+1))+
          ((8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1))-
            (8*signedZ n j-9*((2:Int)^(n+2)+2*n+1))) =
          8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1) := by omega
    rw [heq] at hh
    simpa [qNumerator] using hh

theorem q_period_mod_dvd_iff (n j k : Nat) :
    ((3:Int)^(k+1)∣qNumerator n j) ↔
      ((3:Int)^(k+1)∣qNumerator n (j%depthPeriod k)) := by
  have h:=q_period_dvd_iff n (j%depthPeriod k) k (j/depthPeriod k)
  have he:j%depthPeriod k+(j/depthPeriod k)*depthPeriod k=j :=
    Nat.mod_add_div' j (depthPeriod k)
  rw [he] at h
  exact h

theorem q_small_digit_unique (n k : Nat)
    (hn:n%6=4 ∨ n%6=5) (t:Nat) (ht:t<3) :
    ((3:Int)^(k+2)∣qNumerator n
      (qDepthResidue n k+t*depthPeriod k)) ↔
    t=henselDigit
      (qNumerator n (qDepthResidue n k)/(3:Int)^(k+1))
      (8*(2*n+3:Int)*(2:Int)^(qDepthResidue n k+1)*depthCoeff k) := by
  let b:=qDepthResidue n k
  let a : Int := 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  let q : Int := qNumerator n b/(3:Int)^(k+1)
  have ha:a%3≠0:=by simpa [a] using qCoeff_unit n b k hn
  have hbase:=qDepthResidue_good n k hn
  have hc:=q_lift_criterion n b k t ht hbase
  constructor
  · intro hh
    have hd:(3:Int)∣q-a*t:=hc.mp hh
    exact henselDigit_div q a ha t ht hd
  · intro ht'
    subst t
    apply hc.mpr
    exact henselDigit_divides q a ha


end CascadeQDepthHensel
