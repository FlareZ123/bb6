import Std

/-- If two negative-gap first-evaluator residues hold for the same odd
constant C, their exponents are separated by at least twice the smaller
power of three. -/
theorem negative_gap_exponents_separated
    {C A B : Nat}
    (hAB : A < B)
    (hC : 2*B ≤ C)
    (hA : (C-2*A) % 3^(A+1) = 3^A)
    (hB : (C-2*B) % 3^(B+1) = 3^B) :
    B-A ≥ 2*3^A := by
  have hdouble : 2*(B-A) ≥ 4*3^A := by
    have hdiv1 : 3^(A+1) ∣ 3^(B+1) :=
      Nat.pow_dvd_pow 3 (Nat.succ_le_succ (Nat.le_of_lt hAB))
    have hdiv2 : 3^(A+1) ∣ 3^B :=
      Nat.pow_dvd_pow 3 (Nat.succ_le_of_lt hAB)
    have hN2 : (C-2*B) % 3^(A+1) = 0 := by
      calc
        (C-2*B) % 3^(A+1) = ((C-2*B) % 3^(B+1)) % 3^(A+1) := by
          rw [Nat.mod_mod_of_dvd (C-2*B) hdiv1]
        _ = 3^B % 3^(A+1) := by rw [hB]
        _ = 0 := Nat.mod_eq_zero_of_dvd hdiv2
    have hsum : C-2*A = (C-2*B) + 2*(B-A) := by omega
    have hdiffmod : (2*(B-A)) % 3^(A+1) = 3^A := by
      calc
        (2*(B-A)) % 3^(A+1) = ((C-2*B) + 2*(B-A)) % 3^(A+1) := by
          rw [Nat.add_mod, hN2]
          simp
        _ = (C-2*A) % 3^(A+1) := by rw [← hsum]
        _ = 3^A := hA
    have hpow : 3^(A+1) = 3*3^A := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hlt4 : 2*(B-A) < 4*3^A
    · by_cases hlt3 : 2*(B-A) < 3*3^A
      · have hrem : (2*(B-A)) % 3^(A+1) = 2*(B-A) := by
          rw [hpow]
          exact Nat.mod_eq_of_lt hlt3
        rw [hrem] at hdiffmod
        have hoddPow : ∀ n : Nat, 3^n % 2 = 1 := by
          intro n
          induction n with
          | zero => decide
          | succ n ih =>
              rw [Nat.pow_succ, Nat.mul_mod]
              simp
              exact ih
        have hodd : 3^A % 2 = 1 := hoddPow A
        have heven : (2*(B-A)) % 2 = 0 := by simp
        omega
      · have hge3 : 3*3^A ≤ 2*(B-A) := by omega
        have hrem : (2*(B-A)) % 3^(A+1) = 2*(B-A) - 3*3^A := by
          rw [hpow]
          have hltrem : 2*(B-A) - 3*3^A < 3*3^A := by omega
          calc
            (2*(B-A)) % (3*3^A) = ((3*3^A) + (2*(B-A)-3*3^A)) % (3*3^A) := by
              congr 1
              omega
            _ = ((3*3^A) % (3*3^A) + (2*(B-A)-3*3^A) % (3*3^A)) % (3*3^A) := by
              rw [Nat.add_mod]
            _ = ((2*(B-A)-3*3^A) % (3*3^A)) := by simp
            _ = 2*(B-A)-3*3^A := Nat.mod_eq_of_lt hltrem
        have hdiffmod' : (2*(B-A)) % (3*3^A) = 3^A := by
          simpa [hpow] using hdiffmod
        have hrem' : (2*(B-A)) % (3*3^A) = 2*(B-A) - 3*3^A := by
          simpa [hpow] using hrem
        rw [hrem'] at hdiffmod'
        omega
    · omega
  omega
