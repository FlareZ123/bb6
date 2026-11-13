import RayDepthResidue
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

def qNumerator (n j : Nat) : Int :=
  8*signedZ n j - 9*((2:Int)^(n+2)+2*n+1)

theorem q_mod_three_even_iff (n j : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    qNumerator n j%3=0 ↔ j%2=0 := by
  have hmod : qNumerator n j%3 = (8:Int)*(signedZ n j%3)%3 := by
    simp [qNumerator, Int.sub_emod, Int.mul_emod]
  rw [hmod]
  have h := signedZ_mod_three_even_iff n j hn
  constructor
  · intro hz
    have hz' : signedZ n j%3=0 := by omega
    exact h.mp hz'
  · intro hj
    have hz' : signedZ n j%3=0 := h.mpr hj
    simp [hz']

def qDepthResidue (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let b := qDepthResidue n k
      let a : Int := 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := qNumerator n b/(3:Int)^(k+1)
      b+henselDigit q a*depthPeriod k

theorem depthPeriod_pos (k : Nat) : 0<depthPeriod k := by
  change 0<3*3^k
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem depthPeriod_next (k : Nat) :
    depthPeriod (k+1)=3*depthPeriod k := by
  simp only [depthPeriod,Nat.pow_succ]
  omega

theorem qCoeff_unit (n b k : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    (8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)%3 ≡ 0 := by
  let x : Int := (2*n+3:Int)*2:Int)^(b+1)*depthCoeff k
  have hx : x%3≠0 := by simpa [x] using rayCoeff_unit n b k hn
  have h8 : (8:Int)%3=2 := by decide
  have hmul : ((8:Int)*x)%3=((8:Int)%3*(x%3))%3 := Int.mul_emod _ _ _
  have hxform : 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k=(8:Int)*x := by
    dsimp [x]
    ac_rfl
  rw [hxform,hmul,h8]
  intro hz
  have hx0 : x%3=0 := by omega
  exact hx hx0

theorem q_lift_criterion (n b k t : Nat) (ht:t<3)
    (hbase : (3:Int)^(k+1)∣!Numerator n b) :
    (3:Int)^((k+2)∣!Numerator n (b+t*depthPeriod k)) :
      (3:Int)^(k+2) | qNumerator n b-m*(8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)*t) := by
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
