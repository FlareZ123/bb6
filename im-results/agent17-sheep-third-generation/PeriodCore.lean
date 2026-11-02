import Std
namespace BB6Sheep17

/-- A proposed period is certified by one modular exponentiation.
The period does not need to be the *minimal* multiplicative order. -/
theorem pow2_period_step (m p n : Nat) (hp : 2^p % m = 1) :
    2^(n+p) % m = 2^n % m := by
  rw [Nat.pow_add, Nat.mul_mod, hp]
  simp only [Nat.mul_one, Nat.mod_mod]

/-- An unbounded number of repetitions of a verified modular period
leaves the residue of an exponential unchanged. -/
theorem pow2_period_mul (m p n k : Nat) (hp : 2^p % m = 1) :
    2^(n+p*k) % m = 2^n % m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ]
    rw [← Nat.add_assoc n (p*k) p]
    rw [pow2_period_step m p (n+p*k) hp]
    exact ih

#print axioms pow2_period_step
#print axioms pow2_period_mul
end BB6Sheep17
