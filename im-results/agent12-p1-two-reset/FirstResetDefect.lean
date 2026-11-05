import TwoResetPolynomial
import OneResetTwoAdic
import OneResetSourceEq
set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace BB6.Agent12TwoReset
open BB6.Agent28

/-- A normalized first upper/positive-reset/upper segment exports a positive
    dyadic defect. This requires the established polynomial first-word budget
    as a separate hypothesis. It is independent of blank-root reachability. -/
theorem first_reset_has_positive_defect
    (n r l s K Fr Dr Dp Fend : Nat)
    (hn : 46≤n) (hl : 2≤l)
    (hK : K+n+3=7*2^n)
    (hroot : 2^r*Fr+(n+2)=7*2^n)
    (hpre : Fr+Dr+r=K+2)
    (hreset : 2^l*Dp+r=K+Dr)
    (hpost : 2^s*Fend+Dp+r+l=K+2)
    (hweight : 2^(r+l+s)≤24*(n+2)^3) :
    ∃ C N : Nat,
      C≤2*2^(r+l+s) ∧ 0<N ∧ N≤n+(r+l+s)+1 ∧
      Fend+N=7*2^(n-(r+l+s))*C := by
  let x := n+2
  let P := 2^n
  let R := 2^r
  let L := 2^l
  let S := 2^s
  let m := r+l+s
  have hw : 2^m ≤ 24*x^3 := by simpa only [m,x] using hweight
  have h24P : 24*x^3<2^n := by
    have h6 : 20160*x^6 <6*2^n := by
      simpa only [x] using sixth_power_budget n hn
    have hpow : x^3 ≤ x^6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hb : 6*(24*x^3)<6*2^n := by omega
    exact Nat.lt_of_mul_lt_mul_left hb
  have hxP : x <P := by
    have hx : x≤24*x^3 := by
      have hpow := Nat.pow_le_pow_right (by omega : 0<x) (by omega : 1≤3)
      have ht : x≤x^3 := by simpa using hpow
      omega
    dsimp [P]
    omega
  have hRpos : 0<R := Nat.pow_pos (by decide)
  have hLpos : 0<L := Nat.pow_pos (by decide)
  have hR := power_remainder_division n r 7 Fr x (by omega) hxP
    (by simpa only [R,P,x,Nat.add_assoc] using hroot)
  have hRle : R≤x := hR.2
  obtain ⟨u,hu⟩ := hR.1
  have hu' : R*u=x := hu.symm
  have huSmall : u≤x := by
    have ht := Nat.mul_le_mul_right u (show 1≤R by omega)
    have hs : u≤R*u := by simpa using ht
    omega
  have hrsmall : r<n := by
    have hp : 2^r <2^n := by dsimp [R] at hRle; dsimp [P,x] at hxP; omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hp
  let Q := 2^(n-r)
  have hP : P=R*Q := by
    have hi : n=r+(n-r) := by omega
    calc
      P = 2^(r+(n-r)) := congrArg (fun e:Nat=>2^e) hi
      _ = R*Q := Nat.pow_add 2 r (n-r)
  let V := 2*R-1
  have hV : V+1=2*R := by dsimp [V]; omega
  let M := 2*(n+r+2)-u
  have hMsum : M+u=2*(n+r+2) := by dsimp [M]; omega
  have hMpos : 0<M := by omega
  have hMbound : M≤4*x := by dsimp [x]; omega
  have hc : L*Dp+M=(7*V)*Q :=
    source_one_reset_coefficient n r K P R Q u V M Fr Dr L Dp
      (by simpa only [P] using hK)
      (by simpa only [R,P,x,Nat.add_assoc] using hroot)
      hu' hP hV hMsum hpre (by simpa only [L] using hreset) hRpos
  have hRM : R*M≤4*x^2 := by
    have hh := Nat.mul_le_mul hRle hMbound
    have he : x*(4*x)=4*x^2 := by simp only [Nat.pow_succ,Nat.pow_zero]; ac_rfl
    simpa only [he] using hh
  have hMsmall : M<Q := by
    have hb : 4*x^2 <P := by
      have ht := fourth_power_budget n hn
      have hpow : x^2≤x^4 := Nat.pow_le_pow_right (by omega) (by omega)
      dsimp [P,x] at *
      omega
    have hp : R*M<R*Q := by rw [←hP]; omega
    exact Nat.lt_of_mul_lt_mul_left hp
  have hL := power_remainder_division (n-r) l (7*V) Dp M
     hMpos hMsmall (by simpa only [L,Q,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hc)
  have hLbound : L≤4*x := by omega
  have hlsmall : l<n-r :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp
      (show 2^l<2^(n-r) by dsimp [L,Q] at *; omega)
  have hrl : r+l<n := by omega
  obtain ⟨h,hh⟩ := hL.1
  have hhSmall : h≤x := by
    have h4 : 4≤L := by
      have ha : (2:Nat)^2≤2^l := Nat.pow_le_pow_right (by decide) hl
      simpa only [show (2:Nat)^2=4 by decide, L] using ha
    have hcmp : 4*h≤L*h := Nat.mul_le_mul_right h h4
    have hmax : L*h≤4*x := by rw [←hh]; exact hMbound
    exact Nat.le_of_mul_le_mul_left (by omega : 4*h≤4*x) (by decide)
  let N0 := n+r+l+1-h
  have hN0sum : N0+h=n+r+l+1 := by dsimp [N0]; omega
  have hN0pos : 0<N0 := by omega
  have hN0bound : N0≤6*x := by dsimp [x]; omega
  let Q2 := 2^(n-r-l)
  have hP2 : P=(R*L)*Q2 := by
    have he : n=(r+l)+(n-r-l) := by omega
    calc
      P = 2^((r+l)+(n-r-l)) := congrArg (fun e:Nat=>2^e) he
      _ = (R*L)*Q2 := by rw [Nat.pow_add, Nat.pow_add]
  have hQ : Q=L*Q2 := by
    have he : n-r=l+(n-r-l) := by omega
    calc
      Q = 2^(l+(n-r-l)) := congrArg (fun e:Nat=>2^e) he
      _ = L*Q2 := Nat.pow_add 2 l (n-r-l)
  let Vstar := R*L-V
  have hCpos : V≤R*L := by
    have h4 : 4≤L := by
      have ha : (2:Nat)^2≤2^l := Nat.pow_le_pow_right (by decide) hl
      simpa only [show (2:Nat)^2=4 by decide, L] using ha
    have ht := Nat.mul_le_mul_left R h4
    dsimp [V]
    omega
  have hCsum : Vstar+V=R*L := by dsimp [Vstar]; omega
  have hreset2 : L*Dp+M=(7*V)*(L*Q2) := by rw [←hQ]; exact hc
  have hsuff : S*Fend+N0=(7*Vstar)*Q2 :=
    source_one_reset_suffix_coefficient n r l K P R L Q2 M h N0 V Vstar Dp
      (S*Fend) S Fend
      (by simpa only [P] using hK) hP2 hreset2
      (by simpa only [L] using hh) hN0sum hCsum
      (by simpa only [S] using hpost) rfl hLpos
  have hmLess : m <n := by
    have ht : 2^m<2^n := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp ht
  have hqm : n-r-l = s+(n-m) := by dsimp [m] at *; omega
  have hQ2 : Q2=S*2^(n-m) := by
    dsimp [Q2,S]
    rw [hqm, Nat.pow_add]
  have hSdivQ2 : S∣Q2 := ⟨2^(n-m), hQ2⟩
  have hSN0 : S∣N0 := by
    have hd : S∣(7*Vstar)*Q2 := Nat.dvd_trans hSdivQ2 (Nat.dvd_mul_left Q2 (7*Vstar))
    have hs : S∣S*Fend := Nat.dvd_mul_right S Fend
    exact (Nat.dvd_add_iff_right hs).mpr (hsuff ▸ hd)
  obtain ⟨N,hSN⟩ := hSN0
  have hNpos : 0<N := by
    rw [hSN] at hN0pos
    by_cases hz : N=0
    · simp only [hz,Nat.mul_zero] at hN0pos
      omega
    · omega
  have hNbound : N≤n+m+1 := by
    have hNle : N≤S*N := by
      have ht := Nat.mul_le_mul_right N (show 1≤S by exact Nat.pow_pos (by decide))
      simpa using ht
    rw [hSN] at hN0bound hN0sum
    dsimp [m]
    omega
  have hCbound : Vstar≤2*2^m := by
    have he : R*L*S=2^m := by
      dsimp [R,L,S,m]
      rw [Nat.pow_add, Nat.pow_add]
    have ht : Vstar≤R*L := by omega
    have hOne : R*L≤R*L*S := by
      have hpos : 1≤S := Nat.pow_pos (by decide)
      have ht := Nat.mul_le_mul_left (R*L) hpos
      simpa only [Nat.mul_one] using ht
    omega
  have hfull : Fend+N=7*2^(n-m)*Vstar := by
    rw [hSN,hQ2] at hsuff
    have ht : S*(Fend+N)=S*(7*2^(n-m)*Vstar) := by
      calc
        _ = S*Fend+S*N := by rw [Nat.mul_add]
        _ = (7*Vstar)*(S*2^(n-m)) := hsuff
        _ = S*(7*2^(n-m)*Vstar) := by ac_rfl
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide)) ht
  exact ⟨Vstar,N,hCbound,hNpos,hNbound,hfull⟩

#print axioms first_reset_has_positive_defect
end BB6.Agent12TwoReset
