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

/-- All exponent classes need only a complete finite cycle of k-residues.
A genuine period p need not be the *minimal* multiplicative order. -/
theorem pow2_class_reduce (m p M r k : Nat) (hp : 2^p % m = 1) :
    2^(r+M*k) % m = 2^(r+M*(k%p)) % m := by
  have hk : k = k%p + p*(k/p) := (Nat.mod_add_div k p).symm
  have hmul : M*k = M*(k%p)+p*(M*(k/p)) := by
    calc
      M*k = M*(k%p+p*(k/p)) := congrArg (fun z : Nat => M*z) hk
      _ = M*(k%p)+p*(M*(k/p)) := by rw [Nat.mul_add]; congr 1; ac_rfl
  have he : r+M*k = r+M*(k%p) + p*(M*(k/p)) := by
    rw [hmul]
    omega
  rw [he]
  exact pow2_period_mul m p (r+M*(k%p)) (M*(k/p)) hp

/-- The optimized certificate only needs to assert one genuine full-class
period: 2^(M*q) % m = 1. This eliminates any need to trust a library gcd
calculation or the minimality of a candidate period. -/
theorem pow2_class_reduce_checked (m M r q k : Nat)
    (hq : 2^(M*q) % m = 1) :
    2^(r+M*k) % m = 2^(r+M*(k%q)) % m := by
  have hk : k = k%q + q*(k/q) := (Nat.mod_add_div k q).symm
  have hmul : M*k = M*(k%q)+(M*q)*(k/q) := by
    calc
      M*k = M*(k%q+q*(k/q)) := congrArg (fun z : Nat => M*z) hk
      _ = M*(k%q)+(M*q)*(k/q) := by rw [Nat.mul_add]; ac_rfl
  have he : r+M*k = r+M*(k%q) + (M*q)*(k/q) := by
    rw [hmul]
    omega
  rw [he]
  exact pow2_period_mul m (M*q) (r+M*(k%q)) (k/q) hq

#print axioms pow2_period_step
#print axioms pow2_period_mul
#print axioms pow2_class_reduce
#print axioms pow2_class_reduce_checked
end BB6Sheep17
