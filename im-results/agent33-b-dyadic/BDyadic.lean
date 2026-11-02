import BDyadicCore

namespace BB6.OneDim

theorem parity_flip_on_dyadic_shift (n z : Nat) :
    (iterG n (z+2^n))%2 = 1-(iterG n z)%2 := by
  rw [iterG_critical_shift]
  have hodd : (3^n)%2=1 := by
    induction n with
    | zero => decide
    | succ n ih => simp [Nat.pow_succ, Nat.mul_mod, ih]
  omega

theorem parity_preserved_earlier (n z i : Nat) (hi : i<n) :
    (iterG i (z+2^n))%2 = (iterG i z)%2 := by
  have h : n-i+i=n := by omega
  have hs : iterG i (z+2^n) = iterG i z + 3^i*2^(n-i) := by
    simpa [h] using (iterG_dyadic_shift i (n-i) 1 z)
  rw [hs]
  have hpos : 0<n-i := by omega
  have heven : 2 ∣ 2^(n-i) := by
    cases hm : n-i with
    | zero => omega
    | succ m =>
        rw [Nat.pow_succ]
        exact ⟨2^m, by simp [Nat.mul_comm]⟩
  obtain ⟨w,hw⟩:=heven
  have heq : 3^i * 2^(n-i) = 2*(3^i*w) := by
    rw [hw]
    ac_rfl
  rw [heq]
  omega

theorem arbitrary_finite_parity_word (bits : Nat → Nat)
    (hb : ∀ i, bits i ≤ 1) (n : Nat) :
    ∃ z : Nat, z < 2^n ∧
      ∀ i : Nat, i < n → (iterG i z)%2=bits i := by
  induction n with
  | zero => exact ⟨0, by decide, by intro i hi; omega⟩
  | succ n ih =>
      obtain ⟨z,hz,hr⟩ := ih
      have hpow : 2^(n+1) = 2*2^n := by simp [Nat.pow_succ, Nat.mul_comm]
      by_cases hcurrent : (iterG n z)%2 = bits n
      · refine ⟨z, ?_, ?_⟩
        · rw [hpow]; omega
        · intro i hi
          by_cases hlt : i<n
          · exact hr i hlt
          · have heq : i=n := by omega
            simpa only [heq] using hcurrent
      · refine ⟨z+2^n, ?_, ?_⟩
        · rw [hpow]; omega
        · intro i hi
          by_cases hlt : i<n
          · rw [parity_preserved_earlier n z i hlt]
            exact hr i hlt
          · have heq : i=n := by omega
            subst i
            rw [parity_flip_on_dyadic_shift]
            have hbit := hb n
            have hm : (iterG n z)%2≤1 := by omega
            omega

#print axioms parity_flip_on_dyadic_shift
#print axioms parity_preserved_earlier
#print axioms arbitrary_finite_parity_word
end BB6.OneDim
