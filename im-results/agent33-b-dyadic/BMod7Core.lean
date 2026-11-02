import BDyadic
namespace BB6.OneDim

/-- Parity-dependent branch offsets disappear modulo seven. -/
theorem G_mod7 (z : Nat) : (G z + 1)%7 = (5*(z+1))%7 := by
  simp only [G]
  omega

/-- Exact globally predictable seven-residue after any iteration depth. -/
theorem iterG_mod7 (n z : Nat) :
    (iterG n z+1)%7 = (5^n*(z+1))%7 := by
  induction n generalizing z with
  | zero => simp [iterG]
  | succ n ih =>
      change (iterG n (G z)+1)%7 = (5^(n+1)*(z+1))%7
      rw [ih]
      rw [Nat.pow_succ]
      have h := G_mod7 z
      calc
        (5^n*(G z+1))%7 = ((5^n)%7 * ((G z+1)%7))%7 := Nat.mul_mod _ _ _
        _ = ((5^n)%7 * ((5*(z+1))%7))%7 := by rw [h]
        _ = (5^n*(5*(z+1)))%7 := (Nat.mul_mod _ _ _).symm
        _ = ((5^n*5)*(z+1))%7 := by rw [Nat.mul_assoc]

theorem iterG_zero_mod7 (n : Nat) : (iterG n 0+1)%7 = 5^n%7 := by
  simpa using iterG_mod7 n 0

#print axioms iterG_mod7
end BB6.OneDim
