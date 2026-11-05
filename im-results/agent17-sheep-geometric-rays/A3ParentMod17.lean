import Std
namespace SheepA3

theorem pow2_8 (t : Nat) : (2:Nat)^(8*t+4) % 17 = 16 := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod]
  simp (config := { decide := true })

#print axioms pow2_8
end SheepA3
