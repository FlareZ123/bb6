import Std
set_option exponentiation.threshold 100000

namespace Sheep648Period

/-- A checked finite modulus-power period controls every later exponent. -/
theorem pow_mod_period (m p r k : Nat) (hm : 1 < m)
    (hp : 2^p % m = 1) :
    2^(r+p*k) % m = 2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m, hp]
  simp [Nat.mod_eq_of_lt hm]

/-- A complete cycle of q modular witnesses proves all-k exclusion. -/
theorem no_mod_zero_from_period (modulus p R M q b : Nat)
    (hm : 1 < modulus) (hq : 0 < q)
    (hp : 2^p % modulus = 1)
    (hpdiv : p ∣ M*q)
    (hbase : ∀ t < q, (2^(R+M*t)+b) % modulus ≠ 0) :
    ∀ k, (2^(R+M*k)+b) % modulus ≠ 0 := by
  intro k
  let t := k % q
  have ht : t < q := Nat.mod_lt k hq
  obtain ⟨w, hw⟩ := hpdiv
  have hk : k = t + q*(k/q) := by
    simpa [t, Nat.mul_comm] using (Nat.mod_add_div k q).symm
  have he : R+M*k = (R+M*t)+p*(w*(k/q)) := by
    calc
      R+M*k = R+M*(t+q*(k/q)) := congrArg (fun x => R+M*x) hk
      _ = (R+M*t)+(M*q)*(k/q) := by
        simp only [Nat.mul_add, Nat.mul_assoc]
        omega
      _ = (R+M*t)+p*(w*(k/q)) := by
        rw [hw]
        simp [Nat.mul_assoc]
  have hmod : 2^(R+M*k) % modulus = 2^(R+M*t) % modulus := by
    rw [he]
    exact pow_mod_period modulus p (R+M*t) (w*(k/q)) hm hp
  have hcalc : (2^(R+M*k)+b) % modulus =
      (2^(R+M*t)+b) % modulus := by
    rw [Nat.add_mod, hmod, ←Nat.add_mod]
  rw [hcalc]
  exact hbase t ht

#print axioms pow_mod_period
#print axioms no_mod_zero_from_period

end Sheep648Period
