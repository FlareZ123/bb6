import Agent10Shift

namespace BB6.Agent10B

/-- Shifting the input by 2^n preserves all earlier parity digits. -/
theorem G_prefix_shift (n x : Nat) :
    ∀ j : Nat, j<n → (iterG j (x+2^n))%2=(iterG j x)%2 := by
  have hd : 2^n ∣ (x+8+2^n)-(x+8) := by
    refine ⟨1, ?_⟩
    omega
  have hpre := prefix_if_dvd n (x+8) (x+8+2^n) (by omega) hd
  intro j hj
  have h := hpre j hj
  have hx : (x+8+2^n) = (x+2^n)+8 := by omega
  rw [hx, orbit_shifted, orbit_shifted] at h
  omega

/-- Every prescribed binary n-prefix occurs below the full modulus 2^n. -/
theorem all_binary_prefixes_realized (n : Nat)
    (bits : Nat → Nat) (hbits : ∀ j, bits j ≤ 1) :
    ∃ x : Nat, x<2^n ∧
      ∀ j : Nat, j<n → (iterG j x)%2=bits j := by
  induction n with
  | zero =>
    refine ⟨0, by decide, ?_⟩
    intro j hj
    omega
  | succ n ih =>
    obtain ⟨x,hx,hp⟩:=ih
    have hmax : 2^(n+1)=2*(2^n) := by
      simp [Nat.pow_succ, Nat.mul_comm]
    by_cases hn : (iterG n x)%2=bits n
    · refine ⟨x, ?_, ?_⟩
      · omega
      · intro j hj
        by_cases heq : j=n
        · subst j
          exact hn
        · exact hp j (by omega)
    · refine ⟨x+2^n, ?_, ?_⟩
      · omega
      · intro j hj
        by_cases heq : j=n
        · subst j
          have hf := G_shifted_bit_flip n x
          have hb := hbits n
          have hmod : (iterG n x)%2 < 2 := Nat.mod_lt _ (by decide)
          omega
        · have hf := G_prefix_shift n x j (by omega)
          have hg := hp j (by omega)
          omega

#print axioms G_prefix_shift
#print axioms all_binary_prefixes_realized
end BB6.Agent10B
