import BResetMod7Constraints
namespace BB6.OneDim

/-- A zero sampled bit is equivalent to a forbidden next synthetic reset residue. -/
theorem sampled_zero_iff_bad_reset_mod7 (n : Nat) :
    (iterG (scalarA n) 0)%2=0 ↔
      (scalarA (n+1))%7=0 ∨ (scalarA (n+1))%7=6 := by
  let z := iterG (scalarA n) 0
  have h7 : z%7=4 ∨ z%7=5 := sampled_mod7_four_or_five n
  constructor
  · intro h0
    have hnext : scalarA (n+1) = z+9 := by
      have hh : z%2=0 := h0
      change z+9-3*(z%2)=z+9
      rw [hh]
      omega
    rw [hnext]
    rcases h7 with h4 | h5
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · intro hb
    have h01 : z%2=0 ∨ z%2=1 := by omega
    rcases h01 with h0 | h1
    · exact h0
    · exfalso
      have hnext : scalarA (n+1) = z+6 := by
        change z+9-3*(z%2)=z+6
        rw [h1]
        omega
      rw [hnext] at hb
      rcases h7 with h4 | h5
      · rcases hb with h | h <;> omega
      · rcases hb with h | h <;> omega

theorem scalar_sample_zero_iff_index_mod7 :
    (∃ n : Nat, (iterG (scalarA n) 0)%2=0) ↔
      (∃ n : Nat, (scalarA (n+1))%7=0 ∨ (scalarA (n+1))%7=6) := by
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,(sampled_zero_iff_bad_reset_mod7 n).mp hn⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,(sampled_zero_iff_bad_reset_mod7 n).mpr hn⟩

#print axioms sampled_zero_iff_bad_reset_mod7
end BB6.OneDim
