import Std

namespace SheepWord

theorem coprime_expansion_no_infinite_chain
    (L N : Nat) (hL : 1 < L) (hcop : L.Coprime N)
    (d : Nat → Nat) (hpos : 0 < d 0)
    (hrec : ∀ i, L * d (i+1) = N * d i) : False := by
  have hdvd : ∀ n i, L^n ∣ d i := by
    intro n
    induction n with
    | zero =>
        intro i
        simp
    | succ n ih =>
        intro i
        obtain ⟨k, hk⟩ := ih (i+1)
        have hx : L^(n+1) ∣ L * d (i+1) := by
          refine ⟨k, ?_⟩
          rw [hk]
          simp only [Nat.pow_succ]
          ac_rfl
        rw [hrec i] at hx
        exact (hcop.pow_left (n+1)).dvd_of_dvd_mul_left hx
  have hlarge : d 0 < L^(d 0) := Nat.lt_pow_self hL
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd hpos (hdvd (d 0) 0))) hlarge

/-- A finite run of `n` identical affine blocks forces a large dyadic divisor
of the first increment. The recurrence is imposed only on the first `n`
links; no assumption about any continuation is used. -/
theorem finite_chain_gap_divisibility
    (L N n : Nat) (hcop : L.Coprime N)
    (d : Nat → Nat) (hrec : ∀ i < n, L * d (i+1) = N * d i) :
    L^n ∣ d 0 := by
  have hdvd : ∀ k i, i + k ≤ n → L^k ∣ d i := by
    intro k
    induction k with
    | zero =>
        intro i _
        simp
    | succ k ih =>
        intro i hbound
        have hstep : i < n := by omega
        obtain ⟨q, hq⟩ := ih (i+1) (by omega)
        have hh : L^(k+1) ∣ L * d (i+1) := by
          refine ⟨q, ?_⟩
          rw [hq]
          simp only [Nat.pow_succ]
          ac_rfl
        rw [hrec i hstep] at hh
        exact (hcop.pow_left (k+1)).dvd_of_dvd_mul_left hh
  exact hdvd n 0 (by omega)

/-- The first increment is at least the denominator power, for a positive
finite repeated-block run. This excludes run length greater than its
initial increment's logarithmic size. -/
theorem finite_chain_gap_lower_bound
    (L N n : Nat) (hcop : L.Coprime N)
    (d : Nat → Nat) (hpos : 0 < d 0)
    (hrec : ∀ i < n, L * d (i+1) = N * d i) :
    L^n ≤ d 0 :=
  Nat.le_of_dvd hpos (finite_chain_gap_divisibility L N n hcop d hrec)

#print axioms finite_chain_gap_divisibility
#print axioms finite_chain_gap_lower_bound

#print axioms coprime_expansion_no_infinite_chain
end SheepWord

namespace SheepWord

theorem coprime_affine_no_infinite_growth
    (L N : Nat) (B : Int) (hL : 1 < L) (hcop : L.Coprime N)
    (x : Nat → Nat) (hinc : ∀ i, x i < x (i+1))
    (haff : ∀ i, (L:Int) * x (i+1) = (N:Int) * x i + B) : False := by
  let d : Nat → Nat := fun i => x (i+1) - x i
  have hpos : 0 < d 0 := Nat.sub_pos_of_lt (hinc 0)
  have hrec : ∀ i, L * d (i+1) = N * d i := by
    intro i
    have h0 := haff i
    have h1 := haff (i+1)
    have hdi : ((d i : Nat) : Int) = (x (i+1):Int) - x i := by
      dsimp [d]
      have hi := hinc i
      omega
    have hdi1 : ((d (i+1) : Nat) : Int) = (x (i+2):Int) - x (i+1) := by
      dsimp [d]
      have heq : i+1+1=i+2 := by omega
      simp only [heq]
      have hi : x (i+1) < x (i+2) := by simpa [heq] using hinc (i+1)
      omega
    have hdiff : (L:Int) * ((x (i+2):Int) - x (i+1)) = (N:Int) * ((x (i+1):Int) - x i) := by
      calc
        _ = (L:Int) * x (i+2) - (L:Int) * x (i+1) := by simp [Int.mul_sub]
        _ = ((N:Int) * x (i+1) + B) - ((N:Int) * x i + B) := by rw [h1, h0]
        _ = (N:Int) * ((x (i+1):Int) - x i) := by simp [Int.mul_sub]; omega
    rw [← hdi, ← hdi1] at hdiff
    exact Int.ofNat.inj (show ((L*d (i+1):Nat):Int) = ((N*d i:Nat):Int) from by
      simpa only [Int.natCast_mul] using hdiff)
  exact coprime_expansion_no_infinite_chain L N hL hcop d hpos hrec

#print axioms coprime_affine_no_infinite_growth
end SheepWord
