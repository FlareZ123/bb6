import ExceptionalCost
namespace BB6.Agent8Exceptional
open BB6.Agent28

/-- A word has spent zero inverse cost exactly at its initial root. -/
theorem OddWord.zero_cost_iff_zero_coefficient
    {K D m A T : Nat} (h : OddWord K D m A T) : m=0 ↔ A=0 := by
  cases h with
  | base => decide
  | @next D m A T D' l h hl hstep =>
      have hp : 0 < (2:Nat)^m := Nat.pow_pos (by decide)
      constructor
      · intro hm0; omega
      · intro ha0; omega

/-- The coefficients of exact nontrivial dyadic words skip 2. -/
theorem OddWord.coefficient_ne_two
    {K D m A T : Nat} (h : OddWord K D m A T) : A ≠ 2 := by
  cases h with
  | base => decide
  | @next D m A T D' l h hl hstep =>
      by_cases hm : m=0
      · have hA : A=0 := (OddWord.zero_cost_iff_zero_coefficient h).mp hm
        simp [hm,hA]
      · have hA : 1 ≤ A := by
          have hiff := OddWord.zero_cost_iff_zero_coefficient h
          by_cases hz : A=0
          · have hh : m=0 := hiff.mpr hz
            omega
          · omega
        have hpow : 2 ≤ (2:Nat)^m := by
          have hp : (2:Nat)^1 ≤ (2:Nat)^m :=
            Nat.pow_le_pow_right (by decide) (by omega)
          simpa using hp
        omega

private theorem double_n_le_pow (n : Nat) (hn : 4≤n) : 2*n≤2^n := by
  have h : ∀ t : Nat, 2*(t+4) ≤ (2:Nat)^(t+4) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have hp : (2:Nat)^((t+1)+4) = 2*(2^(t+4)) := by
          rw [show (t+1)+4=(t+4)+1 by omega, Nat.pow_succ]
          omega
        omega
  have heq : (n-4)+4=n := by omega
  simpa [heq] using h (n-4)

/-- The critical P1 root cannot reach the exceptional d=5 boundary
    until four more inverse costs than its exponent have accumulated. -/
theorem OddWord.exceptional_needs_n_plus_four
    (n K m A T : Nat) (hn : 14 ≤ n)
    (hK : K+n+3=7*2^n)
    (h : OddWord K 2 m A T) : n+4≤m := by
  have hweak := OddWord.exceptional_needs_n_plus_two n K m A T hn hK h
  have hmass := h.mass_identity
  have hmom := OddWord.moment_le h
  have hApos : 1 ≤ A := by
    by_cases ha : 1≤A
    · exact ha
    · have hz : A=0 := by omega
      simp [hz] at hmass
      have hp : 1≤(2:Nat)^m := Nat.one_le_pow m 2 (by decide)
      omega
  have hA1 : A ≠ 1 := by
    intro ha
    have hp : (2:Nat)^(n+3) ≤ 2^(m+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h8 : (2:Nat)^(n+3) = 8*2^n := by
      simp [Nat.pow_add, Nat.mul_comm]
    have hpow : 2^m*2= (2:Nat)^(m+1) := by rw [Nat.pow_succ]
    simp [ha] at hmass
    omega
  have hA2 := OddWord.coefficient_ne_two h
  have hA3 : 3≤A := by omega
  by_cases hgoal : n+4≤m
  · exact hgoal
  · have hm : m≤n+3 := by omega
    have hp : (2:Nat)^(m+1) ≤ 16*2^n := by
      calc
        2^(m+1) ≤ 2^(n+4) := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 16*2^n := by simp [Nat.pow_add, Nat.mul_comm]
    have hdoub := double_n_le_pow n (by omega)
    have hP : 16≤(2:Nat)^n := by
      have hh : (2:Nat)^4≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using hh
    have hKge : m≤K := by omega
    have hdiff : K=(K-m)+m := by omega
    have hineq : 16*2^n < 3*(K-m) := by omega
    have hKprod : (K-m)*A + m*A=K*A := by
      calc
        (K-m)*A + m*A = (K-m+m)*A := by simp [Nat.add_mul]
        _ = K*A := by rw [←hdiff]
    have hKA : K*A≤2^(m+1)+m*A := by
      have hpow : 2^m*2=(2:Nat)^(m+1) := by rw [Nat.pow_succ]
      omega
    have hsmall : (K-m)*A≤16*2^n := by omega
    have hthree : 3*(K-m)≤(K-m)*A := by
      have hh:=Nat.mul_le_mul_left (K-m) hA3
      simpa [Nat.mul_comm] using hh
    omega

#print axioms BB6.Agent8Exceptional.OddWord.exceptional_needs_n_plus_four
end BB6.Agent8Exceptional
