import OneResetGrowth
import OneResetTwoAdic

namespace BB6.Agent28

/-- Three exact dyadic cancellation equations force a polynomial bound
    on the total upper/reset/upper inverse-word cost. -/
theorem one_reset_triple_cancellation_budget
    (n r l s Fr Dp Fend M N V C : Nat)
    (hn : 30 ≤ n)
    (hMpos : 0 < M) (hNpos : 0 < N)
    (hMbound : M ≤ 4*(n+2))
    (hNbound : N ≤ 6*(n+2))
    (hroot : 2^r*Fr+(n+2)=7*2^n)
    (hreset : 2^l*Dp+M=(7*V)*2^(n-r))
    (hsuffix : 2^s*Fend+N=(7*C)*2^(n-r-l)) :
    2^(r+l+s) ≤ 24*(n+2)^3 := by
  let x := n+2
  let R := 2^r
  let L := 2^l
  let S := 2^s
  have hbig : 24*x^3*(24*x+3) < 7*2^n := by
    simpa only [x] using quartic_growth n hn
  have hf : 7 ≤ 24*x+3 := by omega
  have h4 : 4*x^2 < 2^n := by
    have hle : 7*(24*x^3) ≤ 24*x^3*(24*x+3) := by
      have h := Nat.mul_le_mul_left (24*x^3) hf
      simpa only [Nat.mul_comm 7 (24*x^3)] using h
    have hlt : 24*x^3 < 2^n :=
      Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hle hbig)
    have hxpow : x^2 ≤ x^3 := Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 3)
    omega
  have h24 : 24*x^3 < 2^n := by
    have hle : 7*(24*x^3) ≤ 24*x^3*(24*x+3) := by
      have h := Nat.mul_le_mul_left (24*x^3) hf
      simpa only [Nat.mul_comm 7 (24*x^3)] using h
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hle hbig)
  have hxP : x < 2^n := by
    have hxpow : x^1 ≤ x^2 :=
      Nat.pow_le_pow_right (show 0<x by omega) (by omega : 1 ≤ 2)
    have hxpow' : x ≤ x^2 := by simpa using hxpow
    omega
  have hbR := power_remainder_division n r 7 Fr x (by omega) hxP
    (by simpa only [x,R] using hroot)
  have hRle : R ≤ x := hbR.2
  have hrlt : r < n := by
    have hp : 2^r < 2^n := by dsimp [R] at hRle; omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hp
  have hpR : 2^n = R*2^(n-r) := by
    have hidx : n=r+(n-r) := by omega
    calc
      _ = 2^(r+(n-r)) := congrArg (fun e:Nat=>2^e) hidx
      _ = R*2^(n-r) := Nat.pow_add 2 r (n-r)
  have hRM : R*M ≤ 4*x^2 := by
    calc
      _ ≤ x*(4*x) := Nat.mul_le_mul hRle hMbound
      _ = 4*x^2 := by simp only [Nat.pow_succ, Nat.pow_zero]; ac_rfl
  have hMq : M < 2^(n-r) := by
    have hl : R*M < R*2^(n-r) := by rw [←hpR]; omega
    exact Nat.lt_of_mul_lt_mul_left hl
  have hbL := power_remainder_division (n-r) l (7*V) Dp M hMpos hMq hreset
  have hLle : L ≤ M := hbL.2
  have hLbound : L ≤ 4*x := by omega
  have hln : l < n-r := by
    have hp : 2^l < 2^(n-r) := by dsimp [L] at hLle; omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hp
  have hrl : r+l < n := by omega
  have hpRL : 2^n = (R*L)*2^(n-r-l) := by
    have he : n = (r+l)+(n-r-l) := by omega
    calc
      _ = 2^((r+l)+(n-r-l)) := congrArg (fun e:Nat=>2^e) he
      _ = (R*L)*2^(n-r-l) := by rw [Nat.pow_add, Nat.pow_add]
  have hRLN : (R*L)*N ≤ 24*x^3 := by
    calc
      _ ≤ (x*(4*x))*(6*x) :=
        Nat.mul_le_mul (Nat.mul_le_mul hRle hLbound) hNbound
      _ = 24*x^3 := by simp only [Nat.pow_succ, Nat.pow_zero]; ac_rfl
  have hNq : N < 2^(n-r-l) := by
    have hl : (R*L)*N < (R*L)*2^(n-r-l) := by rw [←hpRL]; omega
    exact Nat.lt_of_mul_lt_mul_left hl
  have hbS := power_remainder_division (n-r-l) s (7*C) Fend N hNpos hNq hsuffix
  have hSle : S ≤ N := hbS.2
  have hSbound : S ≤ 6*x := by omega
  have hbound : (R*L)*S ≤ 24*x^3 := by
    calc
      _ ≤ (x*(4*x))*(6*x) :=
        Nat.mul_le_mul (Nat.mul_le_mul hRle hLbound) hSbound
      _ = 24*x^3 := by simp only [Nat.pow_succ, Nat.pow_zero]; ac_rfl
  have hpowm : 2^(r+l+s) = (R*L)*S := by
    simp only [Nat.pow_add]
    ac_rfl
  simpa only [hpowm, x] using hbound

#print axioms BB6.Agent28.one_reset_triple_cancellation_budget
end BB6.Agent28
