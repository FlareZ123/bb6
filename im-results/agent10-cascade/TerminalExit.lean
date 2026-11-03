import GapCore

namespace TerminalExit

private theorem cross (n : Nat) (hn : 10 ≤ n) :
    (n+1)*(2*(n+1)+3) ≤ 2*(n*(2*n+3)) := by
  have hsq : 10*n ≤ n*n := by
    have h := Nat.mul_le_mul_left n hn
    simpa [Nat.mul_comm] using h
  -- Both sides are quadratic; normalize into a linear inequality over n*n.
  have ha : (n+1)*(2*(n+1)+3) = 2*(n*n)+7*n+5 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have hb : 2*(n*(2*n+3)) = 4*(n*n)+6*n := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem pow_dom (n : Nat) (hn : 10 ≤ n) : 2*n*(2*n+3) ≤ 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h9 : n = 9
    · subst n; decide
    have hn10 : 10 ≤ n := by omega
    have ih := ih hn10
    rw [Nat.pow_succ]
    have hmore := cross n hn10
    calc
      2*(n+1)*(2*(n+1)+3) = 2*((n+1)*(2*(n+1)+3)) := Nat.mul_assoc _ _ _
      _ ≤ 2*(2*(n*(2*n+3))) := Nat.mul_le_mul_left 2 hmore
      _ = 2*(2*n*(2*n+3)) := by rw [Nat.mul_assoc]
      _ ≤ 2*2^n := Nat.mul_le_mul_left 2 ih
      _ = 2^n*2 := Nat.mul_comm _ _

theorem exit_large (n i : Nat) (hn : 10 ≤ n)
    (hexit : 2*2^(n-1)+n < (2*n+3)*2^(i+1)) : n < 2^i := by
  by_cases h : n < 2^i
  · exact h
  have hs : 2^i ≤ n := by omega
  have hp := pow_dom n hn
  have ht : 2*2^(n-1) = 2^n := by
    have hn0 : n-1+1=n := by omega
    calc
      2*2^(n-1) = 2^(n-1+1) := by rw [Nat.pow_succ]; omega
      _ = 2^n := by rw [hn0]
  have hupper : 2^(i+1) = 2*2^i := by rw [Nat.pow_succ]; omega
  rw [ht, hupper] at hexit
  have hmul := Nat.mul_le_mul_left (2*n+3) hs
  have hbound : (2*n+3)*(2*2^i) ≤ (2*n+3)*(2*n) := by
    have htwo := Nat.mul_le_mul_left 2 hs
    exact Nat.mul_le_mul_left (2*n+3) htwo
  have heq : (2*n+3)*(2*n) = 2*n*(2*n+3) := Nat.mul_comm _ _
  omega

theorem exit_index_lt (n i : Nat) (hn : 1 ≤ n)
    (hstay : (2*n+3)*2^i ≤ 2*2^(n-1)+n) : i < n := by
  by_cases h : i < n
  · exact h
  have hi : n ≤ i := by omega
  have hpow : 2^n ≤ 2^i := Nat.pow_le_pow_right (by omega) hi
  have ht : 2*2^(n-1)=2^n := by
    have hn0 : n-1+1=n := by omega
    calc
      2*2^(n-1) = 2^(n-1+1) := by rw [Nat.pow_succ]; omega
      _ = 2^n := by rw [hn0]
  rw [ht] at hstay
  have hpositive : 1 ≤ 2^n := Nat.one_le_pow n 2 (by omega)
  have hprod := Nat.mul_le_mul_left (2*n+2) hpositive
  have heq : (2*n+3)*2^n = 2^n+(2*n+2)*2^n := by
    calc
      (2*n+3)*2^n = ((2*n+2)+1)*2^n := by congr 1 <;> omega
      _ = (2*n+2)*2^n+1*2^n := Nat.add_mul _ _ _
      _ = 2^n+(2*n+2)*2^n := by omega
  have hprod2 := Nat.mul_le_mul_left (2*n+3) hpow
  omega

/-- Every positive-coefficient dyadic prefix crossing has an exact last in-band index. -/
theorem dyadic_exit_exists (k x n : Nat) (_hk : 0 < k)
    (hstart : k ≤ x) (hend : x < k*2^n) :
    ∃ i, i < n ∧ k*2^i ≤ x ∧ x < k*2^(i+1) := by
  induction n with
  | zero => simp at hend; omega
  | succ n ih =>
    by_cases h : x < k*2^n
    · obtain ⟨i, hi, hlow, hupp⟩ := ih h
      exact ⟨i, by omega, hlow, hupp⟩
    · refine ⟨n, by omega, ?_, ?_⟩
      · omega
      · simpa [Nat.pow_succ] using hend

/-- The exact dyadic departure exists for every n≥10. -/
theorem exact_exit_exists (n : Nat) (hn : 10 ≤ n) :
    ∃ i, (2*n+3)*2^i ≤ 2*2^(n-1)+n ∧
      2*2^(n-1)+n < (2*n+3)*2^(i+1) := by
  have hp := pow_dom n hn
  have h2 : n < 2^n := Nat.lt_pow_self (by omega : 1 < 2)
  have htop : 2*2^(n-1) = 2^n := by
    have hdec : n-1+1=n := by omega
    calc
      2*2^(n-1) = 2^(n-1+1) := by rw [Nat.pow_succ]; omega
      _ = 2^n := by rw [hdec]
  have hstart : 2*n+3 ≤ 2*2^(n-1)+n := by
    rw [htop]
    have h2n : 1 ≤ 2*n := by omega
    have hm := Nat.mul_le_mul_right (2*n+3) h2n
    have hprod : (2*n)*(2*n+3) = 2*n*(2*n+3) := rfl
    omega
  have hend : 2*2^(n-1)+n < (2*n+3)*2^n := by
    rw [htop]
    have hp1 := Nat.one_le_pow n 2 (by omega)
    have hm := Nat.mul_le_mul_left (2*n+2) hp1
    have heq : (2*n+3)*2^n = 2^n+(2*n+2)*2^n := by
      calc
        (2*n+3)*2^n = ((2*n+2)+1)*2^n := by congr 1 <;> omega
        _ = (2*n+2)*2^n+1*2^n := Nat.add_mul _ _ _
        _ = 2^n+(2*n+2)*2^n := by omega
    omega
  obtain ⟨i, hi, hlo, hhi⟩ := dyadic_exit_exists (2*n+3) (2*2^(n-1)+n) n
    (by omega) hstart (by simpa [htop] using hend)
  exact ⟨i, hlo, hhi⟩

/-- The first drop below the dyadic scale lies strictly beyond every smaller band. -/
theorem terminal_exit_band (n i : Nat) (hn : 10 ≤ n)
    (hstay : (2*n+3)*2^i ≤ 2*2^(n-1)+n)
    (hexit : 2*2^(n-1)+n < (2*n+3)*2^(i+1)) :
    4*2^(n-1)-3 < 8*2^(n-1)+n-1-(2*n+3)*2^(i+1) ∧
    8*2^(n-1)+n-1-(2*n+3)*2^(i+1) < 6*2^(n-1)-1 := by
  have hin := exit_index_lt n i (by omega) hstay
  have hs := exit_large n i hn hexit
  have hni : n-i+i=n := by omega
  have hscale : 2*2^(n-1)=2^(n-i)*2^i := by
    have htop : 2*2^(n-1)=2^n := by
      have hh : n-1+1=n := by omega
      calc
        2*2^(n-1) = 2^(n-1+1) := by rw [Nat.pow_succ]; omega
        _ = 2^n := by rw [hh]
    rw [htop, ← Nat.pow_add, hni]
  have heven : 2^(n-i)%2=0 := by
    have hni1 : n-i-1+1=n-i := by omega
    rw [←hni1, Nat.pow_succ]
    simp
  have hodd : (2*n+3)%2=1 := by omega
  have htwice : 2^(i+1) = 2*2^i := by rw [Nat.pow_succ]; omega
  have hlower := GapCore.terminal_lower_gap n (2^(n-1)) (2^i)
    (2^(n-i)) (2*n+3) hs heven hodd hscale hstay
  have hmul : (2*n+3)*(2*2^i) = (2*n+3)*2^(i+1) := by rw [htwice]
  rw [← htwice] at hlower
  constructor
  · exact hlower
  · omega

/-- No dyadic even-reset image band overlaps the open gap. -/
theorem no_even_band (n m t : Nat) (hn : 2 ≤ n)
    (hlo : 4*2^(n-1)-3 < t)
    (hhi : t < 6*2^(n-1)-1) :
    ¬ (6*2^m-1 ≤ t ∧ t ≤ 8*2^m-3) := by
  intro hband
  rcases hband with ⟨ha,hb⟩
  by_cases hm : m < n-1
  · have hpow : 2^(m+1) ≤ 2^(n-1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hdouble : 2*2^m ≤ 2^(n-1) := by
      rw [Nat.pow_succ] at hpow
      omega
    omega
  · have hpow : 2^(n-1) ≤ 2^m := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- Every n>=10 candidate has a specifically located first-band exit,
    ruling out all even-reset predecessors at that terminal height. -/
theorem excluded_index_even_gap (n : Nat) (hn : 10 ≤ n) :
    ∃ i, ∀ m, ¬(6*2^m-1 ≤
      (8*2^(n-1)+n-1-(2*n+3)*2^(i+1)) ∧
      (8*2^(n-1)+n-1-(2*n+3)*2^(i+1)) ≤ 8*2^m-3) := by
  obtain ⟨i, hstay, hexit⟩ := exact_exit_exists n hn
  obtain ⟨hlow, hhigh⟩ := terminal_exit_band n i hn hstay hexit
  exact ⟨i, fun m => no_even_band n m _ (by omega) hlow hhigh⟩

#print axioms excluded_index_even_gap
#print axioms terminal_exit_band
#print axioms pow_dom
#print axioms exit_large
#print axioms exit_index_lt
end TerminalExit
