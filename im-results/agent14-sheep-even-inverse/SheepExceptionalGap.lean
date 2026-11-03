import Std

namespace SheepExceptionalGap

/-- An ample exponential-versus-linear bound, uniform for every exponent >= 141. -/
theorem huge_power (N : Nat) (hN : 141 ≤ N) :
    405*(N+3)+1000 < 2^(N-11) := by
  have hall (t : Nat) :
      405*(141+t+3)+1000 < 2^(130+t) := by
    induction t with
    | zero => decide
    | succ t ih =>
      have hp : 2^(130+(t+1))=2*2^(130+t) := by
        rw [show 130+(t+1)=(130+t)+1 by omega,Nat.pow_succ]
        omega
      have hpos : 0<2^(130+t) := Nat.pow_pos (by omega)
      rw [hp]
      omega
  have ht1 : N=141+(N-141) := by omega
  have ht2 : N-11=130+(N-141) := by omega
  have h := hall (N-141)
  rw [←ht1,←ht2] at h
  exact h

/-- Uniform explicit coefficient-gap theorem for special odd-part-three
predecessors. Once c lies strictly between adjacent powers of two, a linear
correction cannot bridge the exponential gap at these exponent scales. -/
theorem no_exp_linear (N a c D B e : Nat)
    (hN : 141 ≤ N) (he1 : 1 ≤ e) (he11 : e ≤ 11)
    (hclo : 2^(e-1) < c) (hchi : c < 2^e)
    (hD : D ≤ 405) (hB : B ≤ 1000) :
    c*2^a + D*a+B ≠ 2^N := by
  intro hfalse
  have heN : e≤N := by omega
  have hpow : 2^N=2^e*2^(N-e) := by
    calc
      2^N=2^(e+(N-e)) := by congr 1; omega
      _=2^e*2^(N-e) := by rw [Nat.pow_add]
  have hp11 : 2^(N-11) ≤ 2^(N-e) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hhuge := huge_power N hN
  by_cases ha : a≤N-e
  · have hap : 2^a ≤ 2^(N-e) :=
      Nat.pow_le_pow_right (by decide) ha
    have hmp : c*2^a ≤ c*2^(N-e) :=
      Nat.mul_le_mul_left c hap
    have hcoef : c+1 ≤ 2^e := by omega
    have hmp2 : (c+1)*2^(N-e) ≤2^e*2^(N-e) :=
      Nat.mul_le_mul_right (2^(N-e)) hcoef
    have hlin : D*a+B < 2^(N-e) := by
      have hDa : D*a≤405*a := Nat.mul_le_mul_right a hD
      omega
    have hmul : c*2^(N-e)+2^(N-e)=(c+1)*2^(N-e) := by
      rw [Nat.add_mul]
      omega
    omega
  · have ha' : N-e+1 ≤ a := by omega
    have hap : 2^(N-e+1) ≤2^a :=
      Nat.pow_le_pow_right (by decide) ha'
    have hmp : c*2^(N-e+1) ≤ c*2^a :=
      Nat.mul_le_mul_left c hap
    have hexp : 2^e=2*2^(e-1) := by
      calc
        2^e = 2^((e-1)+1) := by congr 1; omega
        _ = 2^(e-1)*2 := by rw [Nat.pow_succ]
        _ = 2*2^(e-1) := by omega
    have hcoef : 2^e<2*c := by omega
    have hpos : 0<2^(N-e) := Nat.pow_pos (by omega)
    have hmul : 2^e*2^(N-e)<(2*c)*2^(N-e) :=
      Nat.mul_lt_mul_of_pos_right hcoef hpos
    have heq : c*2^(N-e+1)=(2*c)*2^(N-e) := by
      rw [show N-e+1=(N-e)+1 by omega,Nat.pow_succ]
      ac_rfl
    omega

#print axioms no_exp_linear
end SheepExceptionalGap
