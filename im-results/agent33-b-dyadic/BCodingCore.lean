import BCodingBalance
namespace BB6.OneDim

/-- Agreement on the first n parity symbols forces congruence modulo 2^n. -/
theorem parity_prefix_divisible (n z w : Nat) (hle : z ≤ w)
    (hpar : ∀ i : Nat, i < n → (iterG i z)%2 = (iterG i w)%2) :
    2^n ∣ w-z := by
  induction n generalizing z w with
  | zero => simp
  | succ n ih =>
      have hp0 : z%2=w%2 := by simpa [iterG] using hpar 0 (by omega)
      have hle' := G_order z w hp0 hle
      have hpar' : ∀ i : Nat, i<n → (iterG i (G z))%2=(iterG i (G w))%2 := by
        intro i hi
        simpa only [iterG] using hpar (i+1) (by omega)
      obtain ⟨q,hq⟩ := ih (G z) (G w) hle' hpar'
      have hg := G_gap z w hp0 hle
      have hthree : 2^(n+1) ∣ 3*(w-z) := by
        refine ⟨q, ?_⟩
        calc
          3*(w-z) = 2*(G w-G z) := hg.symm
          _ = 2*(2^n*q) := by rw [hq]
          _ = 2^(n+1)*q := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have cop : Nat.Coprime (2^(n+1)) 3 := Nat.Coprime.pow_left (n+1) (by decide)
      exact cop.dvd_of_dvd_mul_left hthree

#print axioms parity_prefix_divisible
end BB6.OneDim
