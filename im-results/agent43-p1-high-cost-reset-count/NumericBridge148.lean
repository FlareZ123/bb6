import NumericPower148

namespace BB6.Agent43Numeric148

/-- A uniform finite-integer interval lemma, checked by core arithmetic and
    order monotonicity. The endpoint comparison is an explicit exact integer. -/
private theorem fixed_interval
    (n z lo hi Z : Nat)
    (hlo : lo ≤ n) (hhi : n ≤ hi) (hz : z ≤ Z)
    (hbase : 24^Z*(hi+2)^(2*Z+2) < 2^lo) :
    24^z*(n+2)^(2*z+2) < 2^n := by
  have hzp : 24^z ≤ 24^Z :=
    Nat.pow_le_pow_right (by decide) hz
  have hnp : (n+2)^(2*z+2) ≤ (hi+2)^(2*z+2) :=
    Nat.pow_le_pow_left (by omega) (2*z+2)
  have hnp2 : (hi+2)^(2*z+2) ≤ (hi+2)^(2*Z+2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have htotal : 24^z*(n+2)^(2*z+2) ≤
      24^Z*(hi+2)^(2*Z+2) := by
    exact Nat.mul_le_mul hzp (Nat.le_trans hnp hnp2)
  have hr : 2^lo ≤ 2^n :=
    Nat.pow_le_pow_right (by decide) hlo
  exact Nat.lt_of_le_of_lt htotal (Nat.lt_of_lt_of_le hbase hr)

private theorem triple_pow_dom8 (z : Nat) (hz : 8 ≤ z) :
    2*z+752 ≤ 3*2^z := by
  have H : ∀ k : Nat, 2*(k+8)+752 ≤ 3*2^(k+8) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hidx : (k+1)+8 = (k+8)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have hidx : (z-8)+8=z := by omega
  simpa only [hidx] using H (z-8)

private theorem triple_pow_dom9 (z : Nat) (hz : 9 ≤ z) :
    2*z+1518 ≤ 3*2^z := by
  have H : ∀ k : Nat, 2*(k+9)+1518 ≤ 3*2^(k+9) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hidx : (k+1)+9=(k+9)+1 := by omega
      rw [hidx,Nat.pow_succ]
      omega
  have hidx : (z-9)+9=z := by omega
  simpa only [hidx] using H (z-9)

private theorem finite_148_186 (n z : Nat)
    (hnlo : 148 ≤ n) (hnhi : n ≤ 186)
    (hgate : 3*2^z ≤ 4*n+2*z+6) :
    24^z*(n+2)^(2*z+2) < 2^n := by
  have hz7 : z ≤ 7 := by
    by_cases hshort : z ≤ 7
    · exact hshort
    · have hlong : 8 ≤ z := by omega
      have hdom := triple_pow_dom8 z hlong
      omega
  by_cases h149 : n ≤ 149
  · exact fixed_interval n z 148 149 7 hnlo h149 hz7 (by decide)
  by_cases h163 : n ≤ 163
  · exact fixed_interval n z 150 163 7 (by omega) h163 hz7 (by decide)
  exact fixed_interval n z 164 186 7 (by omega) hnhi hz7 (by decide)

private theorem finite_187_255 (n z : Nat)
    (hnlo : 187 ≤ n) (hnhi : n ≤ 255)
    (hgate : 3*2^z ≤ 4*n+2*z+6) :
    24^z*(n+2)^(2*z+2) < 2^n := by
  have hz8 : z ≤ 8 := by
    by_cases hshort : z ≤ 8
    · exact hshort
    · have hlong : 9 ≤ z := by omega
      have hdom := triple_pow_dom9 z hlong
      omega
  exact fixed_interval n z 187 255 8 hnlo hnhi hz8 (by decide)

private theorem finite_256_511 (n z : Nat)
    (hnlo : 256 ≤ n) (hnhi : n ≤ 511)
    (h2z : 2^z ≤ 4*n) :
    24^z*(n+2)^(2*z+2) < 2^n := by
  have hz10 : z ≤ 10 := by
    by_cases hshort : z ≤ 10
    · exact hshort
    · have hlong : 11 ≤ z := by omega
      have hpow : (2:Nat)^11 ≤ 2^z :=
        Nat.pow_le_pow_right (by decide) hlong
      have h11 : (2:Nat)^11=2048 := by decide
      rw [h11] at hpow
      omega
  exact fixed_interval n z 256 511 10 hnlo hnhi hz10 (by decide)

/-- All-natural arithmetic obstruction, for the genuine source last-reset
    cost conditions. This proof has five exact finite endpoint checks and a
    single infinite dyadic shell induction n>=512. -/
theorem universal_numeric_gap_148 (n z : Nat)
    (hn : 148 ≤ n) (hzle : z ≤ n)
    (hgate : 3*2^z ≤ 4*n+2*z+6) :
    24^z*(n+2)^(2*z+2) < 2^n := by
  by_cases hn186 : n ≤ 186
  · exact finite_148_186 n z hn hn186 hgate
  by_cases hn255 : n ≤ 255
  · exact finite_187_255 n z (by omega) hn255 hgate
  have hn256 : 256 ≤ n := by omega
  have h2z : 2^z ≤ 4*n := by omega
  by_cases hn511 : n ≤ 511
  · exact finite_256_511 n z hn256 hn511 h2z
  exact shell_large_numeric n z (by omega) h2z

#print axioms BB6.Agent43Numeric148.universal_numeric_gap_148

end BB6.Agent43Numeric148
