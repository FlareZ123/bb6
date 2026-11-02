import BResetArithmetic
namespace BB6.OneDim

/-- Every hypothetical reset index avoids residue two modulo three. -/
theorem scalarA_no_two_mod3 (n : Nat) : scalarA n %3≠2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      let z := iterG (scalarA n) 0
      have hn : 0<scalarA n := scalarA_positive n
      have hz : z%3≠2 := iterG_pos_no_two_mod3 (scalarA n) 0 hn
      have hb : z%2=0 ∨ z%2=1 := by omega
      rcases hb with h0 | h1
      · change (z+9-3*(z%2))%3≠2
        rw [h0]
        omega
      · change (z+9-3*(z%2))%3≠2
        rw [h1]
        omega

/-- All samples from the hypothetical reset sequence lie in two residues. -/
theorem sampled_mod7_four_or_five (n : Nat) :
    (iterG (scalarA n) 0)%7=4 ∨ (iterG (scalarA n) 0)%7=5 := by
  exact scalarA_pow7_at_odd_index (scalarA n) (scalarA_odd n) (scalarA_no_two_mod3 n)

#print axioms sampled_mod7_four_or_five
end BB6.OneDim
