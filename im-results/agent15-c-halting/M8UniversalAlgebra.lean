import M8SharpFamily
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- Elementary geometric-series identity underlying the explicit all-odd
    Machine C stopping-input M8 witness family. -/
theorem universal_algebra (B Q H U m d t : Nat)
    (hB : B=3*Q+1)
    (hQ : 1≤Q)
    (hH : B=8*2^d*H)
    (hU : U=m+2^(d+1))
    (_hbound : 3≤B) :
    let J := (B-3)*(U+1)+B*t
    let N := (Q-1)*U+Q*(t+1)
    let V := 2+8*H*N
    3*V*2^d+J+3*m+3=B*(J+3) := by
  let J := (B-3)*(U+1)+B*t
  let N := (Q-1)*U+Q*(t+1)
  let V := 2+8*H*N
  have hBsub : B-3+3=B := by omega
  have hQsub : Q-1+1=Q := by omega
  have hJ : J+3+3*U=B*(U+t+1) := by
    have hmul : (B-3)*(U+1)+3*(U+1)=B*(U+1) := by
      calc
        (B-3)*(U+1)+3*(U+1) = (B-3+3)*(U+1) := (Nat.add_mul (B-3) 3 (U+1)).symm
        _ = B*(U+1) := by rw [hBsub]
    calc
      J+3+3*U = (B-3)*(U+1)+3*(U+1)+B*t := by dsimp [J]; omega
      _ = B*(U+1)+B*t := by rw [hmul]
      _ = B*(U+t+1) := by
        rw [show U+t+1=(U+1)+t by omega]
        simp only [Nat.mul_add, Nat.mul_one]
  have hN : N+U=Q*(U+t+1) := by
    change (Q-1)*U+Q*(t+1)+U=Q*(U+t+1)
    calc
      (Q-1)*U+Q*(t+1)+U = (Q-1+1)*U+Q*(t+1) := by simp only [Nat.add_mul, Nat.one_mul]; ac_rfl
      _ = Q*(U+t+1) := by
        rw [hQsub, show U+t+1=U+(t+1) by omega]
        simp only [Nat.mul_add]
  have hQJ : Q*(J+3) = B*N+U := by
    have hpoly : Q*(J+3)+3*Q*U = B*(N+U) := by
      calc
        Q*(J+3)+3*Q*U=Q*(J+3+3*U) := by simp only [Nat.mul_add, Nat.mul_assoc]; ac_rfl
        _ = Q*(B*(U+t+1)) := by rw [hJ]
        _ = B*(Q*(U+t+1)) := by ac_rfl
        _ = B*(N+U) := by rw [hN]
    have hBQ : B=3*Q+1 := hB
    have hh : B*(N+U)=B*N+3*Q*U+U := by
      rw [hBQ]
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]; ac_rfl
    rw [hh] at hpoly
    omega
  have hV : 3*V*2^d=3*(B*N+2^(d+1)) := by
    have hpow : 2^(d+1)=2*2^d := by rw [Nat.pow_succ]; ac_rfl
    change 3*(2+8*H*N)*2^d=3*(B*N+2^(d+1))
    rw [hH, hpow]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    ac_rfl
  have hmass : Q*(J+3)=m+2^d*V := by
    rw [hQJ,hU]
    have hV' : 2^d*V=B*N+2^(d+1) := by
      have hVV : 3*2^d*V=3*(B*N+2^(d+1)) := by
        calc
          3*2^d*V=3*V*2^d := by ac_rfl
          _=3*(B*N+2^(d+1)) := hV
      rw [Nat.mul_assoc] at hVV
      omega
    omega
  have hBbase : B*(J+3)=3*Q*(J+3)+(J+3) := by
    rw [hB]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]; ac_rfl
  change 3*V*2^d+J+3*m+3=B*(J+3)
  rw [hBbase]
  rw [show 3*Q*(J+3)=3*(Q*(J+3)) by ac_rfl, hmass]
  simp only [Nat.mul_add]
  ac_rfl
end BB6.Agent15Research
