import DRegularFast

namespace BB6.DRegularFast

/-- The residue of `c + A*p` modulo `D` only depends on `p mod D`. -/
theorem residue_mod_of_mod (c A p D : Nat) :
    (c + A*p) % D = (c + A*(p % D)) % D := by
  rw [← Nat.mod_add_div p D]
  simp [Nat.add_mod, Nat.mul_mod]

/-- A quotient by `D` only depends modulo `m` on the input modulo `D*m`.
    This is the arithmetic invariant needed to propagate a 3-adic lift
    residue across one block without materializing the full lifted state. -/
theorem quotient_mod_of_mod_mul (c A p D m : Nat) (hD : 0 < D) :
    ((c + A*p) / D) % m =
      ((c + A*(p % (D*m))) / D) % m := by
  let r := p % (D*m)
  let q := p / (D*m)
  have hp : p = r + D*m*q := by
    dsimp [r,q]
    exact (Nat.mod_add_div p (D*m)).symm
  have hmul : A*(D*m*q) = D*(A*m*q) := by
    simp only [Nat.mul_assoc]
    ac_rfl
  have hnum : c + A*p = (c + A*r) + D*(A*m*q) := by
    rw [hp, Nat.mul_add, hmul]
    simp [Nat.add_assoc]
  have hquot : (c + A*p) / D = (c + A*r) / D + A*m*q := by
    rw [hnum]
    exact Nat.add_mul_div_left (c + A*r) (A*m*q) hD
  rw [hquot]
  simp [r, Nat.add_mod, Nat.mul_mod]

#print axioms residue_mod_of_mod
#print axioms quotient_mod_of_mod_mul

end BB6.DRegularFast
