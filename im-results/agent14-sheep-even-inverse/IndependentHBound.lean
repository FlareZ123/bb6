import Std

namespace SheepIndependentHBound

/-- Exact power period suffices for every natural step k. -/
theorem pow_mod_period (m p r k : Nat) (hm : 1 < m)
    (hp : 2^p % m=1) :
    2^(r+p*k)%m=2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m, hp]
  simp [Nat.mod_eq_of_lt hm]

#print axioms pow_mod_period
end SheepIndependentHBound
