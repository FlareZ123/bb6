import RayDepthResidue
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

def qNumerator (n j : Nat) : Int :=
  8*signedZ n j - 9*((2:Int)^(n+2)+2*n+1)

private theorem q_mod_three_even_iff (n j : Nat)
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

/-- The Q/U numerator has the same unique ternary depth selector as signedZ,
    but with the lift coefficient multiplied by eight. -/
def qDepthResidue (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let b := qDepthResidue n k
      let a : Int := 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := qNumerator n b/(3:Int)^(k+1)
      b+henselDigit q a*depthPeriod k

private theorem depthPeriod_pos (k : Nat) : 0<depthPeriod k := by
  change 0<2*3^k
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

private theorem depthPeriod_next (k : Nat) :
    depthPeriod (k+1)=3*depthPeriod k := by
  simp only [depthPeriod,Nat.pow_succ]
  omega

private theorem qCoeff_unit (n b k : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    (8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)%3 ≠ 0 := by
  let x : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
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

private theorem q_lift_criterion (n b k t : Nat) (ht:t<3)
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
  have hs := signedZ_shift_digit_mod n b k t
      ht
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

private theorem qDepthResidue_lt (n k : Nat) :
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

private theorem qDepthResidue_good (n k : Nat)
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

private theorem q_period_dvd_iff (n j k m : Nat) :
    ((3:Int)^(k+1)∣qNumerator n (j+m*depthPeriod k)) ↔
      ((3:Int)^(k+1)∣qNumerator n j) := by
  have hs := signedZ_period_mul n j k m
  have hmul :
      (8*signedZ n (j+m*depthPeriod k))%(3:Int)^(k+1) =
        (8*signedZ n j)%(3:Int)^(k+1) := by
    simpa only [Int.mul_emod,Int.emod_emod] using
      (congrArg (fun x : Int => (8*x)%(3:Int)^(k+1)) hs)
  have hleft :
      (8*signedZ n (j+m*depthPeriod k)-9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+1) =
      (8*signedZ n j-9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+1) := by
    calc
      _ = ((8*signedZ n (j+m*depthPeriod k))%(3:Int)^(k+1)-
            (9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+1))%(3:Int)^(k+1) := by
              rw [Int.sub_emod]
      _ = ((8*signedZ n j)%(3:Int)^(k+1)-
            (9*((2:Int)^(n+2)+2*n+1))%(3:Int)^(k+1))%(3:Int)^(k+1) := by rw [hmul]
      _ = _ := by rw [←Int.sub_emod]
  have hqmod :
      qNumerator n (j+m*depthPeriod k)%(3:Int)^(k+1) =
        qNumerator n j%(3:Int)^(k+1) := by
    dsimp [qNumerator]
    exact hleft
  constructor
  · intro h
    rw [Int.dvd_iff_emod_eq_zero] at h ⊢
    rw [hqmod] at h
    exact h
  · intro h
    rw [Int.dvd_iff_emod_eq_zero] at h ⊢
    rw [←hqmod] at h
    exact h

private theorem q_period_mod_dvd_iff (n j k : Nat) :
    ((3:Int)^(k+1)∣qNumerator n j) ↔
      ((3:Int)^(k+1)∣qNumerator n (j%depthPeriod k)) := by
  have h:=q_period_dvd_iff n (j%depthPeriod k) k (j/depthPeriod k)
  have he:j%depthPeriod k+(j/depthPeriod k)*depthPeriod k=j :=
    Nat.mod_add_div' j (depthPeriod k)
  rw [he] at h
  exact h

private theorem q_small_digit_unique (n k : Nat)
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

/-- For every precision, Q divisibility selects exactly one depth residue. -/
theorem qDepthResidue_iff (n k j : Nat)
    (hn:n%6=4 ∨ n%6=5) :
    ((3:Int)^(k+1)∣qNumerator n j) ↔
      j%depthPeriod k=qDepthResidue n k := by
  induction k generalizing j with
  | zero =>
      have h:=q_mod_three_even_iff n j hn
      change (3:Int)∣qNumerator n j ↔ j%2=0
      rw [Int.dvd_iff_emod_eq_zero]
      simpa using h
  | succ k ih =>
      let p:=depthPeriod k
      let pn:=depthPeriod (k+1)
      let b:=qDepthResidue n k
      let d:=henselDigit
        (qNumerator n b/(3:Int)^(k+1))
        (8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)
      have hstep:pn=3*p:=depthPeriod_next k
      have hdiv:(3:Int)^(k+1)∣(3:Int)^(k+2):=by
        refine ⟨3,?_⟩
        rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
      constructor
      · intro hx
        have hz:(3:Int)^(k+2)∣qNumerator n (j%pn):=
          (q_period_mod_dvd_iff n j (k+1)).mp hx
        have hlo:(3:Int)^(k+1)∣qNumerator n (j%pn):=by
          cases hz with
          | intro w hw =>
            cases hdiv with
            | intro v hv =>
              refine ⟨v*w,?_⟩
              rw [hw,hv]
              ac_rfl
        have hb:(j%pn)%p=b:=(ih (j%pn)).mp hlo
        have hp:0<p:=depthPeriod_pos k
        have hjlt:j%pn<3*p:=by
          have h:=Nat.mod_lt j (depthPeriod_pos (k+1))
          simpa only [pn,hstep] using h
        have ht:(j%pn)/p<3:=(Nat.div_lt_iff_lt_mul hp).mpr hjlt
        have heq:j%pn=b+((j%pn)/p)*p:=by
          have hh:=Nat.mod_add_div' (j%pn) p
          omega
        have hd':=((q_small_digit_unique n k hn ((j%pn)/p) ht).mp
          (by rw [←heq]; exact hz))
        have hnext:qDepthResidue n (k+1)=b+d*p:=rfl
        have hdnum:(j%pn)/p=d:=by simpa only [b,d] using hd'
        have htarget:j%pn=b+d*p:=by rw [←hdnum]; exact heq
        change j%pn=qDepthResidue n (k+1)
        rw [hnext]
        exact htarget
      · intro hx
        apply (q_period_mod_dvd_iff n j (k+1)).mpr
        rw [hx]
        exact qDepthResidue_good n (k+1) hn

/-- Exactly one residue is selected in each full depth period. -/
theorem qDepthResidue_unique_in_period (n k j : Nat)
    (hn:n%6=4 ∨ n%6=5) (hj:j<depthPeriod k) :
    ((3:Int)^(k+1)∣qNumerator n j) ↔ j=qDepthResidue n k := by
  rw [qDepthResidue_iff n k j hn]
  simp only [Nat.mod_eq_of_lt hj]

/-- Exact n=887 selector values through precision eight. -/
theorem qDepthResidue_887_table :
    qDepthResidue 887 0=0 ∧ qDepthResidue 887 1=0 ∧
    qDepthResidue 887 2=0 ∧ qDepthResidue 887 3=0 ∧
    qDepthResidue 887 4=0 ∧ qDepthResidue 887 5=0 ∧
    qDepthResidue 887 6=486 ∧ qDepthResidue 887 7=3402 := by
  have h0 : (3:Int)^6∣qNumerator 887 0 := by decide
  have h486 : (3:Int)^7∣qNumerator 887 486 := by decide
  have h3402 : (3:Int)^8∣qNumerator 887 3402 := by decide
  have hrez : ∠ k=5, ...