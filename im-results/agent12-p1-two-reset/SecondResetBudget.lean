import TwoResetPolynomial
import OneResetTwoAdic
import DefectTransport
set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

namespace BB6.Agent12TwoReset
open BB6.Agent28

private theorem mul_four (x : Nat) : (24*x^3)*(4*x)=96*x^4 := by
  calc
    _ = (24*4)*(x^3*x) := by ac_rfl
    _ = 96*x^4 := by rw [Nat.pow_succ]; rfl

private theorem mul_six (x : Nat) : (96*x^4)*(6*x)=576*x^5 := by
  calc
    _ = (96*6)*(x^4*x) := by ac_rfl
    _ = 576*x^5 := by rw [Nat.pow_succ]; rfl

/-- Second-reset theorem: a first-subword dyadic defect and exact original
    inverse coefficients exclude the affine wall for all n >= 46.
    The explicit defect hypotheses remain to be discharged at the actual
    first source reset. This theorem alone does not decide P1 or BB(6). -/
theorem second_reset_forbids_wall
    (n m l u K F D Dp Fp C N : Nat)
    (hn : 46 ≤ n) (hl : 2 ≤ l)
    (hK : K+n+3=7*2^n)
    (hfirstweight : 2^m ≤ 24*(n+2)^3)
    (hC : C ≤ 2*2^m)
    (hNpos : 0<N) (hNbound : N≤n+m+1)
    (hdefect : F+N=7*2^(n-m)*C)
    (hpre : F+D+m=K+2)
    (hreset : 2^l*Dp+m=K+D)
    (hpost : 2^u*Fp+Dp+m+l=K+2)
    (hwall : 7*2^n ≤ n+4+2^(m+l+u)*(3*(m+l+u)+2*n+4)) : False := by
  let x := n+2
  let B := 2^m
  let L := 2^l
  let S := 2^u
  let P := 2^n
  have hshort : m ≤ x := first_segment_short n m hn (by simpa only [B,x] using hfirstweight)
  have hxpow : 24*x^3 < P := by
    have hp : x^3 ≤ x^6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hb := sixth_power_budget n hn
    dsimp [x,P]
    dsimp [x] at hp
    omega
  have hmP : B<P := by dsimp [B,P,x] at *; omega
  have hmLess : m<n :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hmP
  let Q := 2^(n-m)
  have hP : P=B*Q := by
    have he : n=m+(n-m) := by omega
    calc
      P = 2^(m+(n-m)) := congrArg (fun e:Nat => 2^e) he
      _ = B*Q := Nat.pow_add 2 m (n-m)
  let V := 2*B-C
  have hV : V+C=2*B := by dsimp [V,B] at *; omega
  let M := 2*(n+m+2)-N
  have hMsum : M+N=2*(n+m+2) := by dsimp [M]; omega
  have hMpos : 0<M := by omega
  have hMbound : M≤4*x := by dsimp [x]; omega
  have hinput : L*Dp+M=7*Q*V :=
    defect_reset_input_identity n m K P B Q C F D N M V L Dp
      (by simpa only [P] using hK) hP hV hMsum
      (by simpa only [Q] using hdefect) hpre
      (by simpa only [L] using hreset)
  have hBM : B*M≤96*x^4 := by
    have hw : B≤24*x^3 := by simpa only [B,x] using hfirstweight
    have h := Nat.mul_le_mul hw hMbound
    rw [mul_four] at h
    exact h
  have hMsmall : M<Q := by
    have hp : B*M<B*Q := by rw [←hP]; have hb := fourth_power_budget n hn; dsimp [P,x] at *; omega
    exact Nat.lt_of_mul_lt_mul_left hp
  have hcancel := power_remainder_division (n-m) l (7*V) Dp M
      hMpos hMsmall (by simpa only [L,Q,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hinput)
  have hLbound : L≤4*x := by omega
  have hlLess : l <n-m :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp
      (show 2^l < 2^(n-m) by dsimp [L,Q] at *; omega)
  have hL4 : 4≤L := by
    have hp : (2:Nat)^2 ≤2^l := Nat.pow_le_pow_right (by decide) hl
    simpa only [show (2:Nat)^2=4 by decide, L] using hp
  obtain ⟨h, hMh⟩ := hcancel.1
  have hh : h≤x := by
    have hp : 4*h≤L*h := Nat.mul_le_mul_right h hL4
    have hq : L*h≤4*x := by rw [←hMh]; exact hMbound
    have hr : 4*h≤4*x := by omega
    exact Nat.le_of_mul_le_mul_left hr (by decide)
  let N2 := n+m+l+1-h
  have hN2sum : N2+h=n+m+l+1 := by dsimp [N2]; omega
  have hN2pos : 0<N2 := by omega
  have hlsmall : l<L := Nat.lt_pow_self (by decide : 1<(2:Nat))
  have hN2bound : N2≤6*x := by omega
  let Q2 := 2^(n-m-l)
  have hP2 : P=B*L*Q2 := by
    have he : n=(m+l)+(n-m-l) := by omega
    calc
      P = 2^((m+l)+(n-m-l)) := congrArg (fun e:Nat=>2^e) he
      _ = B*L*Q2 := by rw [Nat.pow_add, Nat.pow_add]
  have hQ : Q=L*Q2 := by
    have he : n-m=l+(n-m-l) := by omega
    calc
      Q = 2^(l+(n-m-l)) := congrArg (fun e:Nat=>2^e) he
      _ = L*Q2 := Nat.pow_add 2 l (n-m-l)
  let C2 := B*L-V
  have hVle : V≤B*L := by
    have hb : B*4 ≤ B*L := Nat.mul_le_mul_left B hL4
    omega
  have hC2 : C2+V=B*L := by dsimp [C2]; omega
  have hreset2 : L*Dp+M=7*(L*Q2)*V := by rw [←hQ]; exact hinput
  have houtput : S*Fp+N2=7*Q2*C2 :=
    defect_reset_output_identity n m l K P B L Q2 C (S*Fp) Dp N2 M V C2 h
      (by simpa only [P] using hK) hP2 hC2 (by simpa only [L] using hMh)
      hN2sum hreset2 (by simpa only [S] using hpost)
      (Nat.pow_pos (by decide))
  have hBLN : (B*L)*N2≤576*x^5 := by
    have hw : B≤24*x^3 := by simpa only [B,x] using hfirstweight
    have hBL := Nat.mul_le_mul hw hLbound
    have hb : B*L≤96*x^4 := by
      rw [mul_four] at hBL
      exact hBL
    have hp := Nat.mul_le_mul hb hN2bound
    rw [mul_six] at hp
    exact hp
  have hN2small : N2<Q2 := by
    have hp : (B*L)*N2<(B*L)*Q2 := by
      rw [←hP2]
      have hb := fifth_power_budget n hn
      dsimp [x,P] at *
      omega
    exact Nat.lt_of_mul_lt_mul_left hp
  have hlast := power_remainder_division (n-m-l) u (7*C2) Fp N2
      hN2pos hN2small
      (by simpa only [S,Q2,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using houtput)
  have hSbound : S≤6*x := by omega
  have huLess : u<S := Nat.lt_pow_self (by decide : 1<(2:Nat))
  have hLen : m+l+u≤11*x := by omega
  have hWeight : 2^(m+l+u)≤576*x^5 := by
    have he : 2^(m+l+u)=B*L*S := by
      dsimp [B,L,S]
      rw [show m+l+u=(m+l)+u by omega, Nat.pow_add, Nat.pow_add]
    rw [he]
    have hw : B≤24*x^3 := by simpa only [B,x] using hfirstweight
    have hBL := Nat.mul_le_mul hw hLbound
    have hb : B*L≤96*x^4 := by
      rw [mul_four] at hBL
      exact hBL
    have hp := Nat.mul_le_mul hb hSbound
    rw [mul_six] at hp
    exact hp
  exact two_reset_budget_contra n (m+l+u) (2^(m+l+u)) hn
    (by simpa only [x] using hLen)
    (by simpa only [x] using hWeight) hwall

#print axioms second_reset_forbids_wall
end BB6.Agent12TwoReset
