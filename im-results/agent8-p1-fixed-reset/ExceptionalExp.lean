import ExceptionalStrong
namespace BB6.Agent8Exceptional
open BB6.Agent28

/-- Every critical P1 odd word terminating at D=2 has exponentially high
cumulative cost, independently of the number and depth of resets. -/
theorem OddWord.exceptional_exponential_cost
    (n K m A T : Nat) (hn : 14 ≤ n)
    (hK : K+n+3=7*2^n)
    (h : OddWord K 2 m A T) :
    6*2^n ≤ (n+m+3)*2^(m+1-n) := by
  have hm := OddWord.exceptional_needs_n_plus_four n K m A T hn hK h
  let P : Nat := 2^n
  let Q : Nat := 2^(m+1-n)
  have hP : 0 < P := Nat.pow_pos (by decide)
  have hmass := h.mass_identity
  have hmoment := OddWord.moment_le h
  have hA : 1 ≤ A := by
    by_cases ha : 1 ≤ A
    · exact ha
    · have hz : A=0 := by omega
      simp [hz] at hmass
      have hp : 1≤(2:Nat)^m := Nat.one_le_pow m 2 (by decide)
      omega
  have hpow : 2^(m+1) = P*Q := by
    have heq : m+1 = n+(m+1-n) := by omega
    rw [heq, Nat.pow_add]
  have hpow2 : 2^m*2 = 2^(m+1) := by rw [Nat.pow_succ]
  have hKA : K*A+n*A+3*A=7*P*A := by
    have hKmul := congrArg (fun x : Nat => x*A) hK
    change (K+n+3)*A = (7*P)*A at hKmul
    simp only [Nat.add_mul] at hKmul
    omega
  have hkey : 7*P*A+1 = P*Q+(n+3)*A+T := by
    have hh : 2^(m+1)+T=1+K*A := by omega
    rw [hpow] at hh
    have heq : (n+3)*A=n*A+3*A := by simp [Nat.add_mul]
    omega
  have hlarge : 2 ≤ (n+3)*A + T := by
    have hscale := Nat.mul_le_mul_left (n+3) hA
    omega
  have hQA : Q+1 ≤ 7*A := by
    by_cases hyes : Q+1 ≤ 7*A
    · exact hyes
    · have hno : 7*A ≤ Q := by omega
      have hmul := Nat.mul_le_mul_left P hno
      have hh : P*(7*A)=7*P*A := by ac_rfl
      omega
  have hAle : P ≤ (n+m+3)*A := by
    have hmul := Nat.mul_le_mul_left P hQA
    have hsm : (n+3)*A+T ≤ (n+m+3)*A := by
      have heq : (n+m+3)*A=(n+3)*A+m*A := by simp [Nat.add_mul]; omega
      omega
    have heq : P*(7*A)=7*P*A := by ac_rfl
    have hmul' : P*Q+P ≤ 7*P*A := by
      calc
        _ = P*(Q+1) := by simp [Nat.mul_add]
        _ ≤ P*(7*A) := hmul
        _ = _ := heq
    omega
  by_cases hlow : n+m+3 ≤ P
  · have hS : (n+3)*A+T ≤ P*A := by
      have hh := Nat.mul_le_mul_right A hlow
      have heq : (n+m+3)*A=(n+3)*A+m*A := by simp [Nat.add_mul]; omega
      omega
    have hQA6prod : P*(6*A) ≤ P*Q := by
      have heq : P*(6*A) = 6*P*A := by ac_rfl
      have h7 : 7*P*A = 6*P*A+P*A := by
        have heq : 7*P = 6*P+P := by omega
        rw [heq, Nat.add_mul]
      omega
    have hQA6 : 6*A ≤ Q := Nat.le_of_mul_le_mul_left hQA6prod hP
    have hleft := Nat.mul_le_mul_left 6 hAle
    have hright := Nat.mul_le_mul_left (n+m+3) hQA6
    have heqLeft : 6*((n+m+3)*A)=(n+m+3)*(6*A) := by ac_rfl
    have heqRight : (n+m+3)*Q=(n+m+3)*Q := rfl
    dsimp [P,Q] at *
    omega
  · have hhigh : P < n+m+3 := by omega
    have hQ : 6 ≤ Q := by
      have hp : (2:Nat)^5 ≤ 2^(m+1-n) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      dsimp [Q]
      have h32 : (2:Nat)^5=32 := by decide
      omega
    have hleft := Nat.mul_le_mul_left 6 (show P≤n+m+3 by omega)
    have hright := Nat.mul_le_mul_left (n+m+3) hQ
    have hh : 6*(n+m+3)=(n+m+3)*6 := by ac_rfl
    dsimp [P,Q] at *
    omega

#print axioms BB6.Agent8Exceptional.OddWord.exceptional_exponential_cost
end BB6.Agent8Exceptional
