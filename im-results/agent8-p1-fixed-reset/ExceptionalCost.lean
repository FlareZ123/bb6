import OddWordCost

namespace BB6.Agent8Exceptional
open BB6.Agent28

/-- Along an exact inverse word, every binary moment is weighted by a
    prefix cost no greater than the final cost. -/
theorem OddWord.moment_le {K D m A T : Nat} (h : OddWord K D m A T) :
    T ≤ m*A := by
  induction h with
  | base => decide
  | @next D m A T D' l h hl hstep ih =>
      have hm : m ≤ m+l := by omega
      calc
        T + m*2^m ≤ m*A + m*2^m := Nat.add_le_add_right ih _
        _ = m*(A+2^m) := by simp [Nat.mul_add]
        _ ≤ (m+l)*(A+2^m) := Nat.mul_le_mul_right _ hm

/-- An exceptional c=1 predecessor has normalized odd coordinate D=2.
    Its total inverse cost must already be large compared with the root. -/
theorem OddWord.exceptional_cost_bound {K m A T : Nat}
    (h : OddWord K 2 m A T) : K ≤ m + 2^(m+1) := by
  have hmom := OddWord.moment_le h
  have hmass := h.mass_identity
  have hA : 1 ≤ A := by
    by_cases hpos : 1 ≤ A
    · exact hpos
    · have hz : A=0 := by omega
      simp [hz] at hmass
      have hp : 1 ≤ (2:Nat)^m := Nat.one_le_pow m 2 (by decide)
      omega
  have hpow : 2^m*2 = (2:Nat)^(m+1) := by
    rw [Nat.pow_succ]
  have hKA : K*A ≤ 2^(m+1)+m*A := by omega
  by_cases hyes : K ≤ m+2^(m+1)
  · exact hyes
  · have hk : m+2^(m+1)+1 ≤ K := by omega
    have hscaled := Nat.mul_le_mul_right A hk
    have hsplit : (m+2^(m+1)+1)*A = m*A+2^(m+1)*A+A := by
      simp [Nat.add_mul]
    have hP : 2^(m+1) ≤ 2^(m+1)*A := by
      simpa using Nat.mul_le_mul_left (2^(m+1)) hA
    omega

theorem n_le_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      have hp : 1 ≤ (2:Nat)^n := Nat.one_le_pow n 2 (by decide)
      omega

private theorem two_n_small (n : Nat) (hn : 14 ≤ n) :
    2*n+4 < 3*2^n := by
  have hlin := n_le_pow n
  have h16 : (2:Nat)^4 ≤ 2^n :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h16' : 16 ≤ (2:Nat)^n := by simpa using h16
  omega

/-- Source-independent necessary cost for reaching the exceptional odd
    coordinate from the critical P1 root. -/
theorem OddWord.exceptional_needs_n_plus_two
    (n K m A T : Nat) (hn : 14 ≤ n)
    (hK : K+n+3=7*2^n)
    (h : OddWord K 2 m A T) : n+2 ≤ m := by
  have hbound := OddWord.exceptional_cost_bound h
  by_cases hyes : n+2 ≤ m
  · exact hyes
  · have hm : m ≤ n+1 := by omega
    have hp : (2:Nat)^(m+1) ≤ 4*2^n := by
      calc
        2^(m+1) ≤ 2^(n+2) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        _ = 4*2^n := by simp [Nat.pow_add, Nat.mul_comm]
    have hlin := two_n_small n hn
    omega

#print axioms BB6.Agent8Exceptional.OddWord.exceptional_needs_n_plus_two
end BB6.Agent8Exceptional
