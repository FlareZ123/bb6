import OneResetBudget
import OneResetSourceEq

namespace BB6.Agent28

/-- Every exact upper/reset/upper chain has uniformly bounded total dyadic
    inverse cost for n≥30, without relying on extra source guards. -/
theorem exact_one_reset_word_polynomial_budget
    (n r l s K Fr Dr Dp Ff : Nat)
    (hn : 30 ≤ n) (hl : 2 ≤ l)
    (hK : K+n+3=7*2^n)
    (hroot : 2^r*Fr+(n+2)=7*2^n)
    (hpre : Fr+Dr+r=K+2)
    (hreset : 2^l*Dp+r=K+Dr)
    (hpost : 2^s*Ff+Dp+r+l=K+2) :
    2^(r+l+s) ≤24*(n+2)^3 := by
  let x := n+2
  let R := 2^r
  let L := 2^l
  let S := 2^s
  let P := 2^n
  have hbig : 24*x^3*(24*x+3) < 7*P := by
    simpa only [x,P] using quartic_growth n hn
  have hf : 7 ≤ 24*x+3 := by omega
  have h24 : 24*x^3 < P := by
    have hle : 7*(24*x^3) ≤ 24*x^3*(24*x+3) := by
      have h := Nat.mul_le_mul_left (24*x^3) hf
      simpa only [Nat.mul_comm 7 (24*x^3)] using h
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hle hbig)
  have h4 : 4*x^2 < P := by
    have hh : x^2 ≤ x^3 :=
      Nat.pow_le_pow_right (show 0<x by omega) (by decide : 2 ≤ 3)
    omega
  have hxP : x < P := by
    have hh : x^1 ≤ x^2 :=
      Nat.pow_le_pow_right (show 0<x by omega) (by decide : 1 ≤ 2)
    have hh' : x ≤ x^2 := by simpa using hh
    omega
  have hRpos : 0<R := Nat.pow_pos (by decide)
  have hLpos : 0<L := Nat.pow_pos (by decide)
  have hbR := power_remainder_division n r 7 Fr x (by omega) hxP
    (by simpa only [x,P,R] using hroot)
  have hRle : R ≤ x := hbR.2
  obtain ⟨u, hu⟩ := hbR.1
  have hRu : R*u=x := hu.symm
  have hule : u ≤ x := by
    have h := Nat.mul_le_mul_right u (show 1 ≤ R by omega)
    have hq : u ≤ R*u := by simpa using h
    omega
  have hrR : r < R := Nat.lt_pow_self (by decide : 1<(2:Nat))
  have hrlt : r < n := by
    have hp : 2^r < 2^n := by dsimp [R,P] at hRle hxP; omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hp
  let Q := 2^(n-r)
  have hP : P=R*Q := by
    have hidx : n=r+(n-r) := by omega
    calc
      _ = 2^(r+(n-r)) := congrArg (fun e:Nat=>2^e) hidx
      _ = R*Q := Nat.pow_add 2 r (n-r)
  let V := 2*R-1
  have hV : V+1=2*R := by dsimp [V]; omega
  let M := 2*(n+r+2)-u
  have hM : M+u=2*(n+r+2) := by dsimp [M]; omega
  have hMpos : 0<M := by omega
  have hMbound : M≤4*x := by omega
  have hresetcoeff : L*Dp+M=(7*V)*Q :=
    source_one_reset_coefficient n r K P R Q u V M Fr Dr L Dp
      (by simpa only [P] using hK)
      (by simpa only [P,R,Nat.add_assoc] using hroot)
      (by simpa only [x] using hRu)
      hP hV hM hpre hreset hRpos
  have hRM : R*M ≤ 4*x^2 := by
    calc
      _ ≤ x*(4*x) := Nat.mul_le_mul hRle hMbound
      _ = 4*x^2 := by simp only [Nat.pow_succ, Nat.pow_zero]; ac_rfl
  have hMq : M<Q := by
    have hh : R*M < R*Q := by rw [←hP]; omega
    exact Nat.lt_of_mul_lt_mul_left hh
  have hbL := power_remainder_division (n-r) l (7*V) Dp M hMpos hMq
    (by simpa only [L,Q] using hresetcoeff)
  have hLle : L≤M := hbL.2
  have hLbound : L≤4*x := by omega
  have hln : l < n-r := by
    have hp : 2^l < 2^(n-r) := by dsimp [L,Q] at hLle hMq; omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hp
  have hrl : r+l<n := by omega
  let Q2 := 2^(n-r-l)
  have hP2 : P=(R*L)*Q2 := by
    have hidx : n=(r+l)+(n-r-l) := by omega
    calc
      _ = 2^((r+l)+(n-r-l)) := congrArg (fun e:Nat=>2^e) hidx
      _ = (R*L)*Q2 := by rw [Nat.pow_add, Nat.pow_add]
  have hQ : Q=L*Q2 := by
    have hidx : n-r=l+(n-r-l) := by omega
    calc
      _ = 2^(l+(n-r-l)) := congrArg (fun e:Nat=>2^e) hidx
      _ = L*Q2 := Nat.pow_add 2 l (n-r-l)
  obtain ⟨h, hMh⟩ := hbL.1
  have hL4 : 4≤L := by
    have hh : (2:Nat)^2 ≤ 2^l := Nat.pow_le_pow_right (by decide) hl
    simpa only [show (2:Nat)^2=4 by decide, L] using hh
  have hhle : h ≤ x := by
    have hmul : 4*h ≤ L*h := Nat.mul_le_mul_right h hL4
    have hupper : L*h ≤4*x := by simpa only [hMh] using hMbound
    have hfour : 4*h ≤4*x := by omega
    exact Nat.le_of_mul_le_mul_left hfour (by decide)
  let N := n+r+l+1-h
  have hNsum : N+h=n+r+l+1 := by dsimp [N]; omega
  have hNpos : 0<N := by omega
  have hlL : l < L := Nat.lt_pow_self (by decide : 1<(2:Nat))
  have hNbound : N≤6*x := by omega
  let C := R*L-V
  have hRLV : V≤R*L := by
    have hh : R*4 ≤ R*L := Nat.mul_le_mul_left R hL4
    omega
  have hC : C+V=R*L := by dsimp [C]; omega
  have hreset2 : L*Dp+M=(7*V)*(L*Q2) := by rw [←hQ]; exact hresetcoeff
  have hsuffix : S*Ff+N=(7*C)*Q2 :=
    source_one_reset_suffix_coefficient n r l K P R L Q2 M h N V C Dp (S*Ff) S Ff
      (by simpa only [P] using hK) hP2 hreset2 hMh hNsum hC
      (by simpa only [S] using hpost) rfl hLpos
  exact one_reset_triple_cancellation_budget n r l s Fr Dp Ff M N V C hn
    hMpos hNpos (by simpa only [x] using hMbound) (by simpa only [x] using hNbound)
    hroot
    (by simpa only [L,Q] using hresetcoeff)
    (by simpa only [S,Q2] using hsuffix)

/-- For n≥30, an exact one-reset word can never enter the affine wall. -/
theorem exact_one_reset_wall_impossible
    (n r l s K Fr Dr Dp Ff D A T : Nat)
    (hn : 30 ≤ n) (hl : 2 ≤ l)
    (hK : K+n+3=7*2^n)
    (hroot : 2^r*Fr+(n+2)=7*2^n)
    (hpre : Fr+Dr+r=K+2)
    (hreset : 2^l*Dp+r=K+Dr)
    (hpost : 2^s*Ff+Dp+r+l=K+2)
    (hword : OddWord K D (r+l+s) A T)
    (hwall : D+3*(r+l+s)+2*n+4=K) : False := by
  have hbudget := exact_one_reset_word_polynomial_budget n r l s K Fr Dr Dp Ff
    hn hl hK hroot hpre hreset hpost
  have hlow := hword.wall_cost_logarithmic_gap (by omega : 14≤n) hK hwall
  exact polynomial_cost_incompatible_with_wall n (r+l+s) hn hbudget hlow

#print axioms BB6.Agent28.exact_one_reset_word_polynomial_budget
#print axioms BB6.Agent28.exact_one_reset_wall_impossible
end BB6.Agent28
