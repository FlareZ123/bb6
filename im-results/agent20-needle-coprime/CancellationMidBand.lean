import CancellationTopStrip

namespace CancellationMidBand
open CancellationNat CancellationGap CancellationStrip

def geomSum (t : Nat) : Nat → Nat
 | 0 => 0
 | n+1 => geomSum t n + t^n

def certC (A t : Nat) : Nat → Nat
 | 0 => 0
 | r+1 => (A*t)^2*certC A t r
       + 3^(2*r)*(A*t-3)*geomSum t (2*r)
       + 9^r*t^(2*r)*(t*(A-3)-3)

theorem cert_identity (A t r : Nat) (hA : 8 ≤ A) (ht : 2 ≤ t) :
    t^(2*r)*A*P A r = 3^(2*r)*geomSum t (2*r) + (A*t+3)*certC A t r := by
  induction r with
  | zero => simp [P, geomSum, certC]
  | succ r ih =>
    have h1t : 1 ≤ t := by omega
    have hmul : A*1 ≤ A*t := Nat.mul_le_mul_left A h1t
    have hB : 3 ≤ A*t := by omega
    have hBsub : A*t-3+3=A*t := Nat.sub_add_cancel hB
    have hA3 : A-3+3=A := Nat.sub_add_cancel (by omega)
    have hmulA : 2 ≤ A-3 := by omega
    have hmulT : t*2 ≤ t*(A-3) := Nat.mul_le_mul_left t hmulA
    have hTA : 3 ≤ t*(A-3) := by omega
    have hTsub : t*(A-3)-3+3=t*(A-3) := Nat.sub_add_cancel hTA
    have hkey1 : (A*t)^2 = 9 + (A*t+3)*(A*t-3) := by grind
    have hkey2 : t^2*A*(A-3) = 9*(1+t) + (A*t+3)*(t*(A-3)-3) := by grind
    have hpowt : t^(2*(r+1)) = t^(2*r)*t^2 := by
      rw [show 2*(r+1)=2*r+2 by omega, Nat.pow_add]
    have hpow3 : 3^(2*(r+1)) = 3^(2*r)*3^2 := by
      rw [show 2*(r+1)=2*r+2 by omega, Nat.pow_add]
    have hgeom : geomSum t (2*(r+1)) = geomSum t (2*r)+t^(2*r)+t^(2*r+1) := by
      rw [show 2*(r+1)=2*r+2 by omega]
      simp [geomSum, Nat.add_assoc]
    have hzy : 9^r=3^(2*r) := by
      rw [show (9:Nat)=3^2 by decide, Nat.pow_mul]
    simp only [P, certC, hpowt, hpow3, hgeom, hzy]
    simp only [Nat.mul_assoc]
    grind

theorem geomSum_mul (t n : Nat) (ht : 1 ≤ t) :
    geomSum t n * (t-1) + 1 = t^n := by
  induction n with
  | zero => simp [geomSum]
  | succ n ih =>
    have hsub : t-1+1=t := Nat.sub_add_cancel ht
    simp only [geomSum, Nat.pow_succ]
    rw [Nat.add_mul]
    calc
      (geomSum t n * (t-1) + t^n * (t-1)) + 1
          = (geomSum t n * (t-1) + 1) + t^n * (t-1) := by omega
      _ = t^n + t^n * (t-1) := by rw [ih]
      _ = t^n * (1 + (t-1)) := by simp [Nat.mul_add]
      _ = t^n * t := by rw [Nat.add_comm 1 (t-1), hsub]


theorem geomSum_weighted_lt (r t n : Nat) (hr : 1 ≤ r) (ht : 2 ≤ t)
    (hn : n+2 ≤ t) :
    n*geomSum t (2*r) < (n+1)*t^(2*r-1) := by
  let L := geomSum t (2*r-1)
  let T := t^(2*r-1)
  have hlen : 2*r=(2*r-1)+1 := by omega
  have hsplit : geomSum t (2*r)=L+T := by
    dsimp [L,T]
    calc
      geomSum t (2*r) = geomSum t ((2*r-1)+1) := by exact congrArg (geomSum t) hlen
      _ = geomSum t (2*r-1)+t^(2*r-1) := by rw [geomSum]
  have hgeom := geomSum_mul t (2*r-1) (by omega)
  have hgeom' : (t-1)*L+1=T := by
    dsimp [L,T] at hgeom ⊢
    simpa [Nat.mul_comm] using hgeom
  have hn' : n ≤ t-1 := by omega
  have hNL : n*L ≤ (t-1)*L := Nat.mul_le_mul_right L hn'
  have hLT : (t-1)*L < T := by omega
  have hNLT : n*L < T := Nat.lt_of_le_of_lt hNL hLT
  have hsum : n*L+n*T < n*T+T := by omega
  have hfactor : n*T+T=(n+1)*T := by
    rw [Nat.add_mul]
    simp
  have hprod : n*(L+T)<(n+1)*T := by
    rw [Nat.mul_add]
    omega
  have hgoal : n*geomSum t (2*r)<(n+1)*T := by rw [hsplit]; exact hprod
  simpa [T] using hgoal

theorem three_pow_gap (r : Nat) (hr : 2 ≤ r) :
    3^(2*r-1)+5 ≤ 2^(4*r-3) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=1
    · subst r
      decide
    · have hr' : 2 ≤ r := by omega
      have ih' := ih hr'
      have hexp3 : 2*(r+1)-1 = (2*r-1)+2 := by omega
      have hexp2 : 4*(r+1)-3 = (4*r-3)+4 := by omega
      have hpow3 : 3^(2*(r+1)-1)=9*3^(2*r-1) := by
        rw [hexp3, Nat.pow_add]
        simp [show (3:Nat)^2=9 by decide, Nat.mul_comm]
      have hpow2 : 2^(4*(r+1)-3)=16*2^(4*r-3) := by
        rw [hexp2, Nat.pow_add]
        simp [show (2:Nat)^4=16 by decide, Nat.mul_comm]
      rw [hpow3, hpow2]
      have hmul := Nat.mul_le_mul_left 16 ih'
      omega


theorem four_mul_le_pow (a : Nat) (ha : 4 ≤ a) : 4*a ≤ 2^a := by
  have hs := CancellationGap.pow_two_ge_square a ha
  have hm : 4*a ≤ a*a := Nat.mul_le_mul_right a ha
  omega

theorem two_pow_four_r_gt (r : Nat) (hr : 2 ≤ r) :
    2*9^r+5 < 2^(4*r) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=1
    · subst r
      decide
    · have hr' : 2 ≤ r := by omega
      have ih' := ih hr'
      have hleft : 2*9^(r+1)+5 < 9*(2*9^r+5) := by
        rw [Nat.pow_succ]
        omega
      have hmid : 9*(2*9^r+5) < 16*2^(4*r) := by
        have hmul := Nat.mul_lt_mul_of_pos_left ih' (by decide : 0 < 9)
        have hpow : 9*2^(4*r) < 16*2^(4*r) := by
          exact Nat.mul_lt_mul_of_pos_right (by decide : 9<16) (Nat.pow_pos (by decide))
        omega
      have hpow : 16*2^(4*r)=2^(4*(r+1)) := by
        rw [show 4*(r+1)=4*r+4 by omega, Nat.pow_add]
        simp [show (2:Nat)^4=16 by decide, Nat.mul_comm]
      omega

theorem three_pow_ge_two_pow (r : Nat) (hr : 2 ≤ r) :
    2^(2*r) ≤ 3^(2*r-1) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=1
    · subst r
      decide
    · have hr' : 2 ≤ r := by omega
      have ih' := ih hr'
      have hpow2 : 2^(2*(r+1))=4*2^(2*r) := by
        rw [show 2*(r+1)=2*r+2 by omega, Nat.pow_add]
        simp [show (2:Nat)^2=4 by decide, Nat.mul_comm]
      have hpow3 : 3^(2*(r+1)-1)=9*3^(2*r-1) := by
        rw [show 2*(r+1)-1=(2*r-1)+2 by omega, Nat.pow_add]
        simp [show (3:Nat)^2=9 by decide, Nat.mul_comm]
      have hmul : 4*2^(2*r) ≤ 4*3^(2*r-1) := Nat.mul_le_mul_left 4 ih'
      have hscale : 4*3^(2*r-1) ≤ 9*3^(2*r-1) :=
        Nat.mul_le_mul_right (3^(2*r-1)) (by decide : 4≤9)
      rw [hpow2,hpow3]
      omega

theorem pow_two_dvd_three_mul {m x : Nat} (h : 2^m ∣ 3*x) : 2^m ∣ x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have h2pow : 2 ∣ 2^(m+1) := by
      refine ⟨2^m, ?_⟩
      rw [Nat.pow_succ]
      omega
    have hEven : 2 ∣ 3*x := Nat.dvd_trans h2pow h
    have hmod : (3*x)%2=0 := Nat.mod_eq_zero_of_dvd hEven
    have hxmod : x%2=0 := by simpa [Nat.mul_mod] using hmod
    have hxEven : 2 ∣ x := Nat.dvd_of_mod_eq_zero hxmod
    rcases hxEven with ⟨y, hy⟩
    rcases h with ⟨k,hk⟩
    have hcancel : 3*y = 2^m*k := by
      apply Nat.mul_left_cancel (by decide : 0 < 2)
      calc
        2*(3*y) = 3*(2*y) := by omega
        _ = 3*x := by rw [hy]
        _ = 2^(m+1)*k := hk
        _ = 2*(2^m*k) := by simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    have hmy : 2^m ∣ 3*y := ⟨k,hcancel⟩
    have hym := ih hmy
    rcases hym with ⟨z,hz⟩
    refine ⟨z, ?_⟩
    calc
      x = 2*y := hy
      _ = 2*(2^m*z) := by rw [hz]
      _ = 2^(m+1)*z := by simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]


theorem geomSum_pos (t n : Nat) (hn : 1 ≤ n) : 0 < geomSum t n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [geomSum]
    cases n with
    | zero => simp [geomSum]
    | succ n =>
      have hp := ih (by omega)
      omega

theorem pow2_mono (m n : Nat) (h : m ≤ n) : 2^m ≤ 2^n :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem nine_pow_ge_sixteen_sq (r : Nat) (hr : 2≤r) :
    16*r*r ≤ 9^r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=1
    · subst r
      decide
    · have hr' : 2≤r := by omega
      have ih' := ih hr'
      have hlin : r+1 ≤ 3*r := by omega
      have hsq : (r+1)*(r+1) ≤ (3*r)*(3*r) := Nat.mul_le_mul hlin hlin
      have hscale : 16*((r+1)*(r+1)) ≤ 9*(16*r*r) := by
        have hh := Nat.mul_le_mul_left 16 hsq
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
      have hmul : 9*(16*r*r) ≤ 9*9^r := Nat.mul_le_mul_left 9 ih'
      have hpow : 9^(r+1)=9*9^r := by rw [Nat.pow_succ]; simp [Nat.mul_comm]
      have htarget : 16*(r+1)*(r+1)=16*((r+1)*(r+1)) := by simp [Nat.mul_assoc]
      rw [hpow]
      exact Nat.le_trans (by simpa [Nat.mul_assoc] using hscale) hmul


theorem midband_no_parent_of_gap (r s d : Nat) (hr : 2 ≤ r)
    (hs : d ≤ s)
    (hc : (2*r-2)*s ≤ valuationA r-d)
    (hgap : 3^(2*r-1)+5 ≤ 2^d) :
    ¬ (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*P (2^(valuationA r)) r +3 -2*(valuationA r-1+s)) := by
  let a := valuationA r
  let A := 2^a
  let t := 2^s
  let T := t^(2*r)
  let Tbase := t^(2*r-1)
  let S := geomSum t (2*r)
  let n := 3^(2*r-1)
  let u := a-1+s
  let B := 2^(a+s)
  let D := B+3
  let N := A*P A r +3 -2*u
  let Y := 3^(2*r)*S
  let U := (2*u-3)*T
  let Q := U-Y
  let R := n*S
  have haLin : 4*r+3 ≤ a := by dsimp [a]; exact valuationA_linear r
  have ha4 : 4 ≤ a := by omega
  have hdLower : 2*r ≤ d := by
    have h3ge := three_pow_ge_two_pow r hr
    have hpow : 2^(2*r) ≤ 2^d := by omega
    by_cases hlt : d < 2*r
    · have hpowlt := Nat.pow_lt_pow_right (by decide : 1<2) hlt
      omega
    · omega
  have hA8 : 8 ≤ A := by
    dsimp [A]
    have hpow : 2^3 ≤ 2^a := pow2_mono 3 a (by omega)
    have h8 : 2^3=8 := by decide
    rw [h8] at hpow
    exact hpow
  have ht2 : 2 ≤ t := by
    dsimp [t]
    have hpow : 2^1 ≤ 2^s := pow2_mono 1 s (by omega)
    have h2 : 2^1=2 := by decide
    rw [h2] at hpow
    exact hpow
  have ht1 : 1 ≤ t := by omega
  have hsLeA : s ≤ a := by
    have hmul : 2*s ≤ (2*r-2)*s := by
      apply Nat.mul_le_mul_right s
      omega
    dsimp [a] at hc ⊢
    omega
  have hmLower : d ≤ a-(2*r-2)*s := by
    dsimp [a] at hc ⊢
    omega
  let m := a-(2*r-2)*s
  have hmLower' : d ≤ m := by dsimp [m]; exact hmLower
  have hfourA : 4*a ≤ 2^a := four_mul_le_pow a ha4
  have h2uBound : 2*u ≤ 4*a := by
    dsimp [u]
    omega
  have hNoTrunc : 2*u ≤ A*P A r+3 := by
    have hPpos : 0 < P A r := P_pos A r (by dsimp [A]; omega) (by omega)
    have hAP : A ≤ A*P A r := by
      exact Nat.le_mul_of_pos_right A hPpos
    dsimp [A] at hAP ⊢
    omega
  have h2uEq : 2*u-3 = 9^r+2*s := by
    dsimp [u,a]
    have hd := valuationA_double r
    omega
  have h2uA : 2*u-3 < A := by
    have hbound : 2*u-3 ≤ 2*9^r+5 := by
      rw [h2uEq]
      have hs2 : 2*s ≤ 2*a := Nat.mul_le_mul_left 2 hsLeA
      have hd := valuationA_double r
      omega
    have hsmall := two_pow_four_r_gt r hr
    have hpow : 2^(4*r) ≤ 2^a := pow2_mono (4*r) a (by omega)
    dsimp [A]
    omega
  have hcase1z : 2*u-3 < 2*Tbase := by
    have hsmall := two_pow_four_r_gt r hr
    have hcoeff : 3 ≤ 2*r-1 := by omega
    have hs2r : 2*r ≤ s := Nat.le_trans hdLower hs
    have hprod : 3*s ≤ (2*r-1)*s := Nat.mul_le_mul_right s hcoeff
    have hs6 : 4*r ≤ 3*s := by
      have hmul := Nat.mul_le_mul_left 3 hs2r
      omega
    have hexp : 4*r ≤ (2*r-1)*s+1 := by omega
    have hpow : 2^(4*r) ≤ 2^((2*r-1)*s+1) := pow2_mono (4*r) ((2*r-1)*s+1) hexp
    have hbase : 2^((2*r-1)*s+1)=2*Tbase := by
      calc
        2^((2*r-1)*s+1)=2^((2*r-1)*s)*2 := by rw [Nat.pow_succ]
        _ = (2^s)^(2*r-1)*2 := by
          rw [← Nat.pow_mul]
          congr 1
          simp [Nat.mul_comm]
        _ = 2*Tbase := by simp [Tbase,t,Nat.mul_comm]
    have hbound : 2*u-3 ≤ 2*9^r+5 := by
      rw [h2uEq]
      have hs2 : 2*s ≤ 2*a := Nat.mul_le_mul_left 2 hsLeA
      have hd := valuationA_double r
      omega
    have hlt : 2*u-3 < 2^((2*r-1)*s+1) :=
      Nat.lt_of_le_of_lt hbound (Nat.lt_of_lt_of_le hsmall hpow)
    rw [hbase] at hlt
    exact hlt
  have hTpow : T = 2^(2*r*s) := by
    dsimp [T,t]
    rw [← Nat.pow_mul]
    congr 1
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hBpow : A*t=B := by
    dsimp [A,t,B]
    rw [Nat.pow_add]
  have hTbasepow : T=Tbase*t := by
    dsimp [T,Tbase]
    calc
      t^(2*r)=t^((2*r-1)+1) := congrArg (fun e => t^e) (by omega)
      _=t^(2*r-1)*t := by rw [Nat.pow_succ]
  have hSpos : 0<S := by dsimp [S]; exact geomSum_pos t (2*r) (by omega)
  have hSltT : S<T := by
    have hgeom := geomSum_mul t (2*r) ht1
    have hmul0 : geomSum t (2*r)*1 ≤ geomSum t (2*r)*(t-1) :=
      Nat.mul_le_mul_left (geomSum t (2*r)) (by omega)
    have hmul : geomSum t (2*r) ≤ geomSum t (2*r)*(t-1) := by simpa using hmul0
    dsimp [S,T]
    omega
  have hn5 : n+5≤t := by
    dsimp [n,t]
    exact Nat.le_trans hgap (pow2_mono d s hs)
  have hn2 : n+2≤t := by omega
  have hmPow : n+5≤2^m := by
    dsimp [n,m]
    exact Nat.le_trans hgap (pow2_mono d (a-(2*r-2)*s) hmLower)
  have h2sPos : 0<2^s := Nat.pow_pos (by decide : 0<2)
  have hTbasePos : 0<Tbase := by dsimp [Tbase,t]; exact Nat.pow_pos h2sPos
  have htPos : 0<t := by dsimp [t]; exact h2sPos
  have hRbound : R < (n+1)*Tbase := by
    dsimp [R,n,Tbase,S]
    exact geomSum_weighted_lt r t (3^(2*r-1)) (by omega) ht2 (by simpa [n] using hn2)
  have hYpos : 0<Y := by dsimp [Y]; exact Nat.mul_pos (Nat.pow_pos (by decide : 0<3)) hSpos
  have h9pow : 3^(2*r)=9^r := by
    rw [show (9:Nat)=3^2 by decide, Nat.pow_mul]
  have hYltU : Y<U := by
    dsimp [Y,U]
    rw [h9pow, h2uEq]
    have h9pos : 0<9^r := Nat.pow_pos (by decide : 0<9)
    have hlt : 9^r*S < 9^r*T := Nat.mul_lt_mul_of_pos_left hSltT h9pos
    have hle : 9^r*T ≤ (9^r+2*s)*T := Nat.mul_le_mul_right T (by omega)
    exact Nat.lt_of_lt_of_le hlt hle
  have hQpos : 0<Q := by dsimp [Q]; omega
  have hYleU : Y≤U := by omega
  have hQplusY : Q+Y=U := by dsimp [Q]; exact Nat.sub_add_cancel hYleU
  have hcert := cert_identity A t r (by omega) ht2
  have hcert' : T*A*P A r=Y+D*(certC A t r) := by
    dsimp [T,Y,D,S,A,t,B] at hcert ⊢
    rw [← Nat.pow_add] at hcert
    exact hcert
  have hNplus : N+2*u=A*P A r+3 := by
    dsimp [N]
    exact Nat.sub_add_cancel hNoTrunc
  have hNred : N+(2*u-3)=A*P A r := by omega
  have hMul : T*N+U=Y+D*(certC A t r) := by
    calc
      T*N+U = T*N+T*(2*u-3) := by dsimp [U]; simp [Nat.mul_comm]
      _ = T*(N+(2*u-3)) := by rw [← Nat.mul_add]
      _ = T*(A*P A r) := by rw [hNred]
      _ = T*A*P A r := by rw [Nat.mul_assoc]
      _ = Y+D*(certC A t r) := hcert'
  have hEq : T*N+Q=D*(certC A t r) := by
    have hMul' := hMul
    rw [← hQplusY] at hMul'
    omega
  intro hDvd
  have hDpos : 0<D := by dsimp [D,B]; omega
  have hDdivQ : D∣Q := by
    have hTN : D∣T*N := Nat.dvd_mul_left_of_dvd hDvd T
    have hDC : D∣D*(certC A t r) := ⟨certC A t r,rfl⟩
    have hdiff := Nat.dvd_sub hDC hTN
    rw [← hEq, Nat.add_sub_cancel_left] at hdiff
    exact hdiff
  let z := Q/D
  have hz : D*z=Q := by
    have hdiv := Nat.div_mul_cancel hDdivQ
    dsimp [z]
    simpa [Nat.mul_comm] using hdiv
  have hUeq : U=D*z+Y := by
    calc
      U=Q+Y := hQplusY.symm
      _=D*z+Y := by rw [hz]
  have hRpos : 0<R := by dsimp [R,n]; exact Nat.mul_pos (Nat.pow_pos (by decide : 0<3)) hSpos
  by_cases hcase : 2*r*s ≤ a+s
  · let e := 2*r*s
    let M := 2^e
    have hMpow : M=2^e := rfl
    have hMT : M∣T := by
      dsimp [M,e]
      rw [hTpow]
      exact ⟨1, by simp⟩
    have hexp : a+s=e+(a+s-e) := by dsimp [e]; omega
    have hBfact : B=M*2^(a+s-e) := by
      dsimp [B,M,e]
      rw [← Nat.pow_add]
      congr 1
    have hMB : M∣B := ⟨2^(a+s-e), by simpa [Nat.mul_comm] using hBfact⟩
    have hModular : M∣z+R := by
      have hMU : M∣U := by
        dsimp [U]
        exact Nat.dvd_mul_left_of_dvd hMT (2*u-3)
      have hMsum : M∣D*z+Y := by rw [← hUeq]; exact hMU
      have hMBz : M∣B*z := Nat.dvd_mul_right_of_dvd hMB z
      have hSplit : D*z+Y=B*z+(3*z+Y) := by
        dsimp [D]
        rw [Nat.add_mul]
        omega
      have hM3zY : M∣3*z+Y := by
        rw [hSplit] at hMsum
        exact (Nat.dvd_add_right hMBz).mp hMsum
      have hpow3 : 3^(2*r)=3^(2*r-1)*3 := by
        calc
          3^(2*r)=3^((2*r-1)+1) := congrArg (fun e => 3^e) (by omega)
          _=3^(2*r-1)*3 := by rw [Nat.pow_succ]
      have hY : Y=3*R := by
        dsimp [Y,R,n,S]
        rw [hpow3]
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have hM3 : M∣3*(z+R) := by
        have hsum : 3*z+3*R=3*(z+R) := by simp [Nat.mul_add]
        rw [hY, hsum] at hM3zY
        exact hM3zY
      have hpowdiv : 2^e∣3*(z+R) := by simpa [hMpow] using hM3
      simpa using pow_two_dvd_three_mul hpowdiv
    have hTbasepow2 : Tbase=2^((2*r-1)*s) := by
      dsimp [Tbase,t]
      rw [← Nat.pow_mul]
      congr 1
      simp [Nat.mul_comm]
    have hMfact : M=Tbase*t := by
      dsimp [M,e]
      have hcoeff : (2*r-1)+1=2*r := by omega
      have hExp : 2*r*s=(2*r-1)*s+s := by
        calc
          2*r*s=((2*r-1)+1)*s := by rw [hcoeff]
          _=(2*r-1)*s+1*s := by rw [Nat.add_mul]
          _=(2*r-1)*s+s := by simp
      calc
        2^(2*r*s)=2^((2*r-1)*s+s) := congrArg (fun e => 2^e) hExp
        _=2^((2*r-1)*s)*2^s := by rw [Nat.pow_add]
        _=Tbase*t := by rw [hTbasepow2]
    have hTleD : T≤D := by
      have hpow : T≤B := by rw [hTpow]; exact pow2_mono (2*r*s) (a+s) hcase
      dsimp [D]
      omega
    have hUbound : U<D*(2*Tbase) := by
      have hTpos : 0<T := by dsimp [T,t]; exact Nat.pow_pos h2sPos
      have hprod := Nat.mul_lt_mul_of_pos_right hcase1z hTpos
      have hprod' : (2*u-3)*T < (2*Tbase)*T := by simpa [Nat.mul_assoc, Nat.mul_comm] using hprod
      have hupper : (2*Tbase)*T ≤ (2*Tbase)*D := Nat.mul_le_mul_left (2*Tbase) hTleD
      dsimp [U]
      exact Nat.lt_of_lt_of_le hprod' (by simpa [Nat.mul_comm] using hupper)
    have hQbound : Q<D*(2*Tbase) := by
      have hQlt : Q<U := by dsimp [Q]; omega
      exact Nat.lt_trans hQlt hUbound
    have hzbound : z<2*Tbase := by
      have hmul : D*z < D*(2*Tbase) := by rw [hz]; exact hQbound
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hRbound' : R<(t-4)*Tbase := by
      have hn' : n+1≤t-4 := by omega
      have hupper : (n+1)*Tbase ≤ (t-4)*Tbase := Nat.mul_le_mul_right Tbase hn'
      exact Nat.lt_of_lt_of_le hRbound hupper
    have hupperSum : 2*Tbase+(t-4)*Tbase < t*Tbase := by
      have ht5 : 5≤t := Nat.le_trans (Nat.le_add_left 5 n) hn5
      have ht4 : 4≤t := Nat.le_trans (by decide : 4≤5) ht5
      have ht4eq : t-4+4=t := Nat.sub_add_cancel ht4
      have hsub : 2+(t-4) < t := by
        calc
          2+(t-4)=(t-4)+2 := by omega
          _<(t-4)+4 := Nat.add_lt_add_left (by decide : 2<4) (t-4)
          _=t := ht4eq
      have hsum : 2*Tbase+(t-4)*Tbase=(2+(t-4))*Tbase := by rw [Nat.add_mul]
      rw [hsum]
      exact Nat.mul_lt_mul_of_pos_right hsub hTbasePos
    have hsumZR : z+R<2*Tbase+(t-4)*Tbase := by omega
    have hltM : z+R<M := by
      have hlt : z+R<t*Tbase := Nat.lt_trans hsumZR hupperSum
      rw [hMfact]
      simpa [Nat.mul_comm] using hlt
    have hposM : 0<M := by dsimp [M]; exact Nat.pow_pos (by decide)
    have hpos : 0<z+R := Nat.add_pos_right z hRpos
    exact (Nat.not_dvd_of_pos_of_lt hpos hltM) hModular
  · have hcase' : a+s ≤2*r*s := by omega
    let e := a+s
    let M :=2^e
    have hMpow : M=2^e := rfl
    have hMB : M∣B := by dsimp [M,B,e]; exact ⟨1,by simp⟩
    have hexp : 2*r*s=e+(2*r*s-e) := by dsimp [e]; omega
    have hTfact : T=M*2^(2*r*s-e) := by
      calc
        T=2^(2*r*s) := hTpow
        _=2^(e+(2*r*s-e)) := by exact congrArg (fun x => 2^x) (by dsimp [e]; omega)
        _=2^e*2^(2*r*s-e) := by rw [Nat.pow_add]
        _=M*2^(2*r*s-e) := rfl
    have hMT : M∣T := ⟨2^(2*r*s-e), by simpa [Nat.mul_comm] using hTfact⟩
    have hModular : M∣z+R := by
      have hMU : M∣U := by
        dsimp [U]
        exact Nat.dvd_mul_left_of_dvd hMT (2*u-3)
      have hMsum : M∣D*z+Y := by rw [← hUeq]; exact hMU
      have hMBz : M∣B*z := Nat.dvd_mul_right_of_dvd hMB z
      have hSplit : D*z+Y=B*z+(3*z+Y) := by
        dsimp [D]
        rw [Nat.add_mul]
        omega
      have hM3zY : M∣3*z+Y := by
        rw [hSplit] at hMsum
        exact (Nat.dvd_add_right hMBz).mp hMsum
      have hpow3 : 3^(2*r)=3^(2*r-1)*3 := by
        calc
          3^(2*r)=3^((2*r-1)+1) := congrArg (fun e => 3^e) (by omega)
          _=3^(2*r-1)*3 := by rw [Nat.pow_succ]
      have hY : Y=3*R := by
        dsimp [Y,R,n,S]
        rw [hpow3]
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have hM3 : M∣3*(z+R) := by
        have hsum : 3*z+3*R=3*(z+R) := by simp [Nat.mul_add]
        rw [hY, hsum] at hM3zY
        exact hM3zY
      have hpowdiv : 2^e∣3*(z+R) := by simpa [hMpow] using hM3
      simpa using pow_two_dvd_three_mul hpowdiv
    have hTbasepow2 : Tbase=2^((2*r-1)*s) := by
      dsimp [Tbase,t]
      rw [← Nat.pow_mul]
      congr 1
      simp [Nat.mul_comm]
    have hMfact : M=Tbase*2^m := by
      dsimp [M,e]
      have hcoeff : (2*r-2)+1=2*r-1 := by omega
      have hmul : (2*r-1)*s=(2*r-2)*s+s := by
        calc
          (2*r-1)*s=((2*r-2)+1)*s := by rw [hcoeff]
          _=(2*r-2)*s+1*s := by rw [Nat.add_mul]
          _=(2*r-2)*s+s := by simp
      have hsub : a-(2*r-2)*s+(2*r-2)*s=a := Nat.sub_add_cancel (by omega)
      have hexp' : a+s=(2*r-1)*s+m := by
        dsimp [m]
        rw [hmul]
        omega
      calc
        2^(a+s)=2^((2*r-1)*s+m) := by exact congrArg (fun e => 2^e) hexp'
        _=2^((2*r-1)*s)*2^m := by rw [Nat.pow_add]
        _=Tbase*2^m := by rw [hTbasepow2]
    have hUbound : U<D*Tbase := by
      have hTprod := Nat.mul_lt_mul_of_pos_right h2uA (Nat.mul_pos hTbasePos htPos)
      have hleft : (2*u-3)*(Tbase*t) < (2^a)*(Tbase*t) := by simpa [Nat.mul_assoc, Nat.mul_comm] using hTprod
      have hpow : (2^a)*(Tbase*t)=B*Tbase := by
        calc
          (2^a)*(Tbase*t)=(2^a*2^s)*Tbase := by
            dsimp [t]
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _=2^(a+s)*Tbase := by rw [← Nat.pow_add]
          _=B*Tbase := rfl
      have hBD : B<D := by dsimp [D]; omega
      have hupper : B*Tbase<D*Tbase := Nat.mul_lt_mul_of_pos_right hBD hTbasePos
      dsimp [U]
      rw [hTbasepow]
      exact Nat.lt_trans (by simpa [hpow] using hleft) hupper
    have hQbound : Q<D*Tbase := by
      have hQlt : Q<U := by dsimp [Q]; omega
      exact Nat.lt_trans hQlt hUbound
    have hzbound : z<Tbase := by
      have hmul : D*z < D*Tbase := by rw [hz]; exact hQbound
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hRbound' : R<(2^m-4)*Tbase := by
      have hn' : n+1≤2^m-4 := by omega
      have hupper : (n+1)*Tbase≤(2^m-4)*Tbase := Nat.mul_le_mul_right Tbase hn'
      exact Nat.lt_of_lt_of_le hRbound hupper
    have hupperSum : Tbase+(2^m-4)*Tbase < 2^m*Tbase := by
      have hm2 : 2≤m := by omega
      have hpow : 2^2≤2^m := pow2_mono 2 m hm2
      have h4 : 2^2=4 := by decide
      have hpow4 : 4≤2^m := by rw [h4] at hpow; exact hpow
      have hpow4eq : 2^m-4+4=2^m := Nat.sub_add_cancel hpow4
      have hsub : 1+(2^m-4)<2^m := by
        calc
          1+(2^m-4)=(2^m-4)+1 := by omega
          _<(2^m-4)+4 := Nat.add_lt_add_left (by decide : 1<4) (2^m-4)
          _=2^m := hpow4eq
      have hsum : Tbase+(2^m-4)*Tbase=(1+(2^m-4))*Tbase := by simp [Nat.add_mul]
      rw [hsum]
      exact Nat.mul_lt_mul_of_pos_right hsub hTbasePos
    have hsumZR : z+R<Tbase+(2^m-4)*Tbase := by omega
    have hltM : z+R<M := by
      have hlt : z+R<2^m*Tbase := Nat.lt_trans hsumZR hupperSum
      rw [hMfact]
      simpa [Nat.mul_comm] using hlt
    have hposM : 0<M := by dsimp [M]; exact Nat.pow_pos (by decide)
    have hpos : 0<z+R := Nat.add_pos_right z hRpos
    exact (Nat.not_dvd_of_pos_of_lt hpos hltM) hModular


theorem nine_pow_mod8 (k : Nat) : (9^k)%8=1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp [Nat.pow_succ, Nat.mul_mod, ih]

theorem three_pow_odd_mod8 (r : Nat) (hr : 2≤r) :
    (3^(2*r-1))%8=3 := by
  have he : 2*r-1=2*(r-1)+1 := by omega
  have hpow : 3^(2*(r-1))=9^(r-1) := by
    rw [show (9:Nat)=3^2 by decide, ←Nat.pow_mul]
  simp [he, Nat.pow_add, hpow, Nat.mul_mod, nine_pow_mod8]

theorem two_pow_mod3_ne_zero (d : Nat) : (2^d)%3 ≠ 0 := by
  induction d with
  | zero => decide
  | succ d ih =>
    intro hzero
    rw [Nat.pow_succ, Nat.mul_mod] at hzero
    have hlt : (2^d)%3 < 3 := Nat.mod_lt _ (by decide)
    have hne : (2^d)%3 ≠ 0 := ih
    have hcases : (2^d)%3=1 ∨ (2^d)%3=2 := by omega
    rcases hcases with h1 | h2
    · simp [h1] at hzero
    · simp [h2] at hzero

theorem log2_gap_five (r : Nat) (hr : 2≤r) :
    3^(2*r-1)+5 ≤ 2^(Nat.log2 (3^(2*r-1))+1) := by
  let n := 3^(2*r-1)
  let d := Nat.log2 n+1
  have hlt : n<2^d := by
    dsimp [d]
    exact Nat.lt_log2_self
  have h3ge : 2^(2*r) ≤ n := by
    dsimp [n]
    exact three_pow_ge_two_pow r hr
  have hdLower : 2*r ≤ d := by
    have hpow : 2^(2*r) ≤ 2^d := by omega
    by_cases hlt' : d < 2*r
    · have hpowlt := Nat.pow_lt_pow_right (by decide : 1<2) hlt'
      omega
    · omega
  have hnmod8 : n%8=3 := by
    dsimp [n]
    exact three_pow_odd_mod8 r hr
  have h8dvd : 8 ∣ 2^d := by
    have hd3 : 3≤d := by omega
    have he : d=3+(d-3) := by omega
    rw [he, Nat.pow_add]
    refine ⟨2^(d-3), ?_⟩
    simp [show (2:Nat)^3=8 by decide, Nat.mul_comm]
  have hpowmod8 : (2^d)%8=0 := Nat.mod_eq_zero_of_dvd h8dvd
  have hnplus1mod8 : (n+1)%8=4 := by
    simp [Nat.add_mod, hnmod8]
  have hnot1 : 2^d-n ≠ 1 := by
    intro hgap1
    have hEq : 2^d=n+1 := by omega
    have hmod := congrArg (fun x => x%8) hEq
    rw [hpowmod8, hnplus1mod8] at hmod
    omega
  have hnDiv3 : 3∣n := by
    dsimp [n]
    have he : 2*r-1=(2*r-2)+1 := by omega
    rw [he, Nat.pow_succ]
    exact ⟨3^(2*r-2), by simp [Nat.mul_comm]⟩
  have hplus3div : 3∣n+3 := Nat.dvd_add hnDiv3 ⟨1, by omega⟩
  have hnot3 : 2^d-n ≠ 3 := by
    intro hgap3
    have hEq : 2^d=n+3 := by omega
    have hdiv : 3∣2^d := by rw [hEq]; exact hplus3div
    exact two_pow_mod3_ne_zero d (Nat.mod_eq_zero_of_dvd hdiv)
  have h2dvd : 2∣2^d := by
    have hd1 : 1≤d := by omega
    have he : d=1+(d-1) := by omega
    rw [he, Nat.pow_add]
    exact ⟨2^(d-1), by simp⟩
  have hpowmod2 : (2^d)%2=0 := Nat.mod_eq_zero_of_dvd h2dvd
  have hnmod2 : n%2=1 := by
    dsimp [n]
    have he : 2*r-1=2*(r-1)+1 := by omega
    have hpow : 3^(2*(r-1))=9^(r-1) := by
      rw [show (9:Nat)=3^2 by decide, ←Nat.pow_mul]
    have h9 := nine_pow_odd (r-1)
    simp [he, Nat.pow_add, hpow, Nat.mul_mod, h9]
  have hsum : (2^d-n)+n=2^d := Nat.sub_add_cancel (Nat.le_of_lt hlt)
  have hgapmod : (2^d-n)%2=1 := by
    have hmod := congrArg (fun x => x%2) hsum
    rw [Nat.add_mod, hnmod2, hpowmod2] at hmod
    have hltmod : (2^d-n)%2<2 := Nat.mod_lt _ (by decide)
    omega
  have hgap5 : 5≤2^d-n := by
    by_cases hsmall : 2^d-n<5
    · have hcases : 2^d-n=1 ∨ 2^d-n=3 := by omega
      rcases hcases with h1 | h3
      · exact False.elim (hnot1 h1)
      · exact False.elim (hnot3 h3)
    · omega
  have hfinal : n+5≤2^d := by omega
  simpa [n,d] using hfinal


theorem midband_no_parent_conservative (r s : Nat) (hr : 2 ≤ r)
    (hs : 4*r-3 ≤ s)
    (hc : (2*r-2)*s ≤ valuationA r-(4*r-3)) :
    ¬ (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*P (2^(valuationA r)) r +3 -2*(valuationA r-1+s)) := by
  exact midband_no_parent_of_gap r s (4*r-3) hr hs hc (three_pow_gap r hr)


def cancellation_threshold (r : Nat) : Nat := Nat.log2 (3^(2*r-1))+1

theorem midband_interval_nonempty (r : Nat) (hr : 2≤r) :
    (2*r-1)*cancellation_threshold r ≤ valuationA r := by
  let n := 3^(2*r-1)
  let d := cancellation_threshold r
  have hn0 : n≠0 := by dsimp [n]; exact Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3))
  have hlog : Nat.log2 n < 4*r-3 := by
    have hpow : n < 2^(4*r-3) := by
      dsimp [n]
      have hgap := three_pow_gap r hr
      omega
    exact (Nat.log2_lt hn0).mpr hpow
  have hlog' := hlog
  dsimp [n] at hlog'
  have hd : d≤4*r-3 := by dsimp [d,cancellation_threshold]; omega
  have h9 := nine_pow_ge_sixteen_sq r hr
  have ha2 := valuationA_double r
  have hprod : (2*r-1)*(4*r-3) ≤ valuationA r := by
    have h1 : 2*r-1 ≤ 2*r := by omega
    have h2 : 4*r-3 ≤ 4*r := by omega
    have hmul := Nat.mul_le_mul h1 h2
    have hscale := Nat.mul_le_mul_left 2 hmul
    have hnorm : 2*((2*r)*(4*r))=16*r*r := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hbound : 2*((2*r-1)*(4*r-3)) ≤ 9^r+5 := by
      rw [hnorm] at hscale
      omega
    omega
  have hmul := Nat.mul_le_mul_left (2*r-1) hd
  exact Nat.le_trans hmul hprod


theorem midband_no_parent (r s : Nat) (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hc : (2*r-2)*s ≤ valuationA r-cancellation_threshold r) :
    ¬ (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*P (2^(valuationA r)) r +3 -2*(valuationA r-1+s)) := by
  exact midband_no_parent_of_gap r s (cancellation_threshold r) hr hs hc
    (log2_gap_five r hr)


/-- Source-equation interface: the hypothesis is the exact cancellation-form
terminal equation obtained from the original high-level Space Needle source.
This is the same inverse equation used by NeedleGeneralInverse.parent_successor_iff. -/
theorem midband_no_parent_source_equation
    (r s q : Nat) (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hc : (2*r-2)*s ≤ valuationA r-cancellation_threshold r)
    (heq : (2^(valuationA r)+3)*(2*q+3)+9^r =
      (2^(valuationA r))^(2*r)) :
    ¬ (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*(2*q+3)+3-2*(valuationA r-1+s)) := by
  let A := 2^(valuationA r)
  have hA : 3 ≤ A := by
    have ha := valuationA_linear r
    have hp := exp_mono 2 (valuationA r) (by omega)
    have h4 : 2^2=4 := by decide
    dsimp [A]
    rw [h4] at hp
    omega
  have he : (A+3)*P A r+9^r=A^(2*r) := CancellationNat.exact A r hA
  change (A+3)*(2*q+3)+9^r=A^(2*r) at heq
  have hm : (A+3)*(2*q+3)=(A+3)*P A r := by omega
  have hq : 2*q+3=P A r := Nat.mul_left_cancel (by omega : 0<A+3) hm
  have hno := midband_no_parent r s hr hs hc
  simpa [A, ←hq] using hno

#print axioms midband_no_parent_source_equation

#print axioms log2_gap_five
#print axioms midband_interval_nonempty

#print axioms midband_no_parent_of_gap
#print axioms midband_no_parent

end CancellationMidBand
