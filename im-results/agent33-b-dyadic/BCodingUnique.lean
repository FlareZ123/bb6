import BCodingCore
namespace BB6.OneDim

/-- Every length-n parity word is realized by a unique residue modulo 2^n. -/
theorem parity_prefix_unique_residue (bits : Nat → Nat)
    (hb : ∀ i, bits i ≤ 1) (n : Nat) :
    ∃ z : Nat, z < 2^n ∧
      (∀ i : Nat, i < n → (iterG i z)%2=bits i) ∧
      (∀ w : Nat, w < 2^n →
          (∀ i : Nat, i<n → (iterG i w)%2=bits i) → w=z) := by
  obtain ⟨z,hz,hr⟩ := arbitrary_finite_parity_word bits hb n
  refine ⟨z,hz,hr,?_⟩
  intro w hw hs
  rcases Nat.le_total z w with hle | hle
  · have hdiv : 2^n ∣ w-z := parity_prefix_divisible n z w hle (by
      intro i hi
      rw [hr i hi,hs i hi])
    have hgap : w-z < 2^n := by omega
    have heq : w-z=0 := by
      rcases hdiv with ⟨q,hq⟩
      by_cases hq0 : q=0
      · simp [hq0] at hq
        omega
      · have hpos : 0<q := by omega
        have hpow : 0<2^n := Nat.pow_pos (by decide)
        have hmin : 2^n≤2^n*q := Nat.le_mul_of_pos_right (2^n) hpos
        omega
    omega
  · have hdiv : 2^n ∣ z-w := parity_prefix_divisible n w z hle (by
      intro i hi
      rw [hs i hi,hr i hi])
    have hgap : z-w < 2^n := by omega
    rcases hdiv with ⟨q,hq⟩
    by_cases hq0 : q=0
    · simp [hq0] at hq
      omega
    · have hpos : 0<q := by omega
      have hpow : 0<2^n := Nat.pow_pos (by decide)
      have hmin : 2^n≤2^n*q := Nat.le_mul_of_pos_right (2^n) hpos
      omega

#print axioms parity_prefix_unique_residue
end BB6.OneDim
