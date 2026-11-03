import Agent30CrossRadix

namespace BB6.Agent30Cross

/-- Each input class modulo 2^n has one and only one nth-output class modulo 3^n. -/
theorem residues_injective (n x y : Nat) (hx : x < 2^n) (hy : y < 2^n)
    (h : iterG n x % 3^n = iterG n y % 3^n) : x = y := by
  have hh := (iterG_cong n x y 1).mp (by simpa using h)
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hh

/-- Every output residue is represented by an input in the canonical 2^n window. -/
theorem residues_cover (n z : Nat) :
    ∃ x : Nat, x < 2^n ∧ iterG n z % 3^n = iterG n x % 3^n := by
  refine ⟨z % 2^n, Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)), ?_⟩
  simpa only [Nat.mul_one] using
    (iterG_cong n z (z%2^n) 1).mpr (by simp)

/-- A canonical representative of every n-fold output class. -/
theorem residues_range (n z : Nat) :
    (iterG n z % 3^n) = iterG n (z % 2^n) % 3^n := by
  simpa only [Nat.mul_one] using
    (iterG_cong n z (z%2^n) 1).mpr (by simp)

#print axioms residues_injective
#print axioms residues_cover
#print axioms residues_range

end BB6.Agent30Cross
