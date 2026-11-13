import QDepthDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

theorem q_lift_criterion (n b k t : Nat) (ht:t<3)
    (hbase : (3:Int)^(k+1)∣qNumerator n b) :
    (3:Int)^(k+2)∣qNumerator n (b+t*depthPeriod k) ↔
      (3:Int)∣(qNumerator n b/(3:Int)^(k+1)-
        (8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)*t) := by
  let m : Int := (3:Int)^(k+1)
  let a0 : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  let a : Int := 8*a0
  have hmne : m≠0 := by
    change (3:Int)^(k+1)≠0
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM : (3:Int)^(k+2)=(3:Int)*m := by
    dsimp [m]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hs := signedZ_shift_digit_mod n b k t ht
  have hmul :
      (8*signedZ n (b+t*depthPeriod k))%(3:Int)^(k+2) =
        (8*(signedZ n b-m*(a0*t)))%(3:Int)^(k+2) := by
    simpa only [Int.mul_emod,Int.emod_emod] using
      (congrArg (fun x : Int => (8*x)%(3:Int)^(k+2)) hs)
  have hqexpr :
      8*(signedZ n b-m*(a0*t))-9*((2:Int)^(n+2)+2*n+1) =
        (8*signedZ n b-9*((2:Int)^(n+2)+2*n+1))-m*(a*t) := by
    rw [Int.mul_sub]
    have hp : 8*(m*(a0*t))=m*(a*t) := by dsimp [a]; ac_rfl
    rw [hp]
    omega
  have hleft :
      (8*signedZ n (b+t*depthPeriod k)-
        9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+2) =
      (8*(signedZ n b-m*(a0*t))-
        9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+2) := by
    calc
      _ = ((8*signedZ n (b+t*depthPeriod k))%(3:Int)^(k+2) -
            (9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+2))%(3:Int)^(k+2) := by
              rw [Int.sub_emod]
      _ = ((8*(signedZ n b-m*(a0*t)))%(3:Int)^(k+2) -
            (9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+2))%(3:Int)^(k+2) := by rw [hmul]
      _ = _ := by rw [←Int.sub_emod]
  have hqexprMod := congrArg
    (fun x : Int => x%(3:Int)^(k+2)) hqexpr
  have hqmod :
      qNumerator n (b+t*depthPeriod k)%(3:Int)^(k+2) =
        (qNumerator n b-m*(a*t))%(3:Int)^(k+2) := by
    dsimp [qNumerator]
    calc
      _ = (8*signedZ n (b+t*depthPeriod k)-
            9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+2) := rfl
      _ = (8*(signedZ n b-m*(a0*t))-
            9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+2) := hleft
      _ = ((8*signedZ n b-9*((2:Int)^(n+2)+2*n+1))-m*(a*t))%(3:Int)^(k+2) := hqexprMod
      _ = _ := rfl
  have hdiviff :
      (3:Int)^(k+2)∣qNumerator n (b+t*depthPeriod k) ↔
        (3:Int)^(k+2)∣qNumerator n b-m*(a*t) := by
    rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero,hqmod]
  have hquot : m*(qNumerator n b/m)=qNumerator n b :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor : qNumerator n b-m*(a*t)=m*(qNumerator n b/m-a*t) := by
    calc
      _ = m*(qNumerator n b/m)-m*(a*t) := by rw [hquot]
      _ = m*(qNumerator n b/m-a*t) := by rw [Int.mul_sub]
  have hcomm : (3:Int)*m=m*3 := Int.mul_comm _ _
  rw [hdiviff,hfactor,hM,hcomm]
  simpa [a,a0,m,Int.mul_assoc] using
    (Int.mul_dvd_mul_iff_left hmne :
      m*3 ∣ m*(qNumerator n b/m-a*t) ↔ 3 ∣ qNumerator n b/m-a*t)


end CascadeQDepthHensel
