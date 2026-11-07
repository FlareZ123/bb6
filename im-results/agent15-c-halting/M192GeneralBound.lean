import Core192Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

open Agent41M192

private theorem pow_linear_first (m : Nat) : 3*m+12 ≤ 2^(m+4) := by
  induction m with
  | zero => decide
  | succ m ih =>
      calc
        3*(m+1)+12 ≤ 2*(3*m+12) := by omega
        _ ≤ 2*2^(m+4) := Nat.mul_le_mul_left 2 ih
        _ = 2^(m+5) := by simp [Nat.pow_succ, Nat.mul_comm]

private theorem pow_linear_second_base (m : Nat) : m+5 ≤ 2^(m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      calc
        m+1+5 ≤ 2*(m+5) := by omega
        _ ≤ 2*2^(m+3) := Nat.mul_le_mul_left 2 ih
        _ = 2^(m+4) := by simp [Nat.pow_succ, Nat.mul_comm]

private theorem pow_linear_second (m : Nat) (hm : 1≤m) : m+5 ≤ 2^(2*m+2) := by
  have hexp : m+3 ≤ 2*m+2 := by omega
  exact Nat.le_trans (pow_linear_second_base m) (Nat.pow_le_pow_right (by omega) hexp)

/-- Every positive-index first-family parameter has right coordinate at least 8. -/
theorem first_stop_k_ge8 (m k : Nat) (hm : 1≤m)
    (hstop : k+3*m+4=2^(2*m+3)) : 8≤k := by
  have hexp : m+4 ≤ 2*m+3 := by omega
  have hpow : 3*m+12 ≤ 2^(2*m+3) :=
    Nat.le_trans (pow_linear_first m) (Nat.pow_le_pow_right (by omega) hexp)
  omega

/-- Every second-family parameter with positive m has right coordinate at least 10. -/
theorem second_stop_k_ge10 (j m k : Nat) (hm : 1≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : 10≤k := by
  have hpow : m+5 ≤ 2^(2*m+2) := pow_linear_second m hm
  have hprod : (m+5)*(j+3) ≤ 2^(2*m+2)*(j+3) :=
    Nat.mul_le_mul_right (j+3) hpow
  have hmul : (m+5)*(j+3) = m*j + 3*m + 5*j + 15 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hlin : j+3*m+15 ≤ (m+5)*(j+3) := by rw [hmul]; omega
  have hlarge : j+3*m+15 ≤ 2^(2*m+2)*(j+3) := Nat.le_trans hlin hprod
  omega

/-- The m=0 second-family branch is also at least 10 when j is positive. -/
theorem second_stop_k_ge10_m0 (j k : Nat) (hj : 1≤j)
    (hstop : k+j+5=4*(j+3)) : 10≤k := by
  have hlin : j+15 ≤ 4*(j+3) := by omega
  omega

/-- All nonexceptional second-family parameters have k≥10. -/
theorem second_stop_k_ge10_except_00 (j m k : Nat) (hjm : j≠0 ∨ m≠0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : 10≤k := by
  rcases hjm with hj|hm
  · by_cases hm0 : m=0
    · subst m
      have hjpos : 1≤j := by omega
      have heq : k+j+5=4*(j+3) := by simpa using hstop
      exact second_stop_k_ge10_m0 j k hjpos heq
    · have hmpos : 1≤m := by omega
      exact second_stop_k_ge10 j m k hmpos hstop
  · have hmpos : 1≤m := by omega
    exact second_stop_k_ge10 j m k hmpos hstop

/--
The M192 backward invariant excludes c=0 states only when their residue pair
satisfies lowCore. The lower bound on k alone is insufficient.
-/
theorem source_no_c0_lowCore (a k : Nat) (hk : 8≤k)
    (hcore : lowCore (a%192) (k%192)) :
    ¬ BB6CLine.Reach (a,k,0) := by
  intro hreach
  have hnot := source_blank_never_bad a k 0 hreach
  have hbad : bad a k 0 := by
    simp [bad, low, hcore, hk]
  exact hnot hbad

/-- The entire first stopping family lies outside the M192 lowCore slice. -/
theorem first_stop_family_outside_lowCore (k : Nat) :
    ¬ lowCore (1%192) (k%192) := by
  simp [lowCore]

/-- The second-family point (j,m,k)=(0,1,40) is outside the same slice. -/
theorem second_stop_example_outside_lowCore :
    ¬ lowCore (3%192) (40%192) := by
  simp [lowCore]

/-- Conditional exclusion for second-family states covered by lowCore. -/
theorem source_no_second_stop_when_lowCore (j m k : Nat)
    (hjm : j≠0 ∨ m≠0)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hcore : lowCore ((2*j+3)%192) (k%192)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hk : 8≤k := by
    have h10 := second_stop_k_ge10_except_00 j m k hjm hstop
    omega
  exact source_no_c0_lowCore (2*j+3) k hk hcore

#print axioms source_no_c0_lowCore
#print axioms first_stop_k_ge8
#print axioms second_stop_k_ge10_except_00

end BB6.Agent15