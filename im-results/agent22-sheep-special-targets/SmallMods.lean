import Std

namespace Agent22Special

/-- Complete-period binary modular identity; no numerical exponent cutoff. -/
theorem pow_mod_period (m p r k : Nat) (hm : 1 < m)
    (hperiod : (2:Nat)^p % m = 1) :
    (2:Nat)^(r+p*k) % m = (2:Nat)^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  have hp : (((2:Nat)^p)^k)%m = 1 := by
    rw [Nat.pow_mod, hperiod]
    simpa using (Nat.mod_eq_of_lt hm)
  rw [hp]
  simp

/-- No b=1 generic predecessor for target 3*2^(4k+2). -/
theorem no_b1 (k : Nat) : (3*2^(4*k+3)) % 5 ≠ 1 := by
  have he : 4*k+3 = 3+4*k := by omega
  rw [he]
  have hp := pow_mod_period 5 4 3 k (by decide) (by decide)
  have hcalc : (3*2^(3+4*k))%5 = 4 := by
    rw [Nat.mul_mod, hp]
  omega

/-- No b=2 generic predecessor for target 3*2^(4k+2). -/
theorem no_b2 (k : Nat) : (3*2^(4*k+3)) % 9 ≠ 3 := by
  have he : 4*k+3 = 1+2*(2*k+1) := by omega
  have hp : (2:Nat)^(4*k+3)%3 = 2 := by
    rw [he, pow_mod_period 3 2 1 (2*k+1) (by decide) (by decide)]
  omega

/-- No b=3 generic predecessor for target 3*2^(4k+2). -/
theorem no_b3 (k : Nat) : (3*2^(4*k+3)) % 17 ≠ 5 := by
  by_cases hk : k % 2 = 0
  · have he : 4*k+3 = 3+8*(k/2) := by omega
    rw [he]
    have hp := pow_mod_period 17 8 3 (k/2) (by decide) (by decide)
    have hcalc : (3*2^(3+8*(k/2)))%17 = 7 := by
      rw [Nat.mul_mod, hp]
    omega
  · have hk1 : k % 2 = 1 := by omega
    have he : 4*k+3 = 7+8*(k/2) := by omega
    rw [he]
    have hp := pow_mod_period 17 8 7 (k/2) (by decide) (by decide)
    have hcalc : (3*2^(7+8*(k/2)))%17 = 10 := by
      rw [Nat.mul_mod, hp]
    omega

/-- No b=4 generic predecessor for target 3*2^(4k+2). -/
theorem no_b4 (k : Nat) : (3*2^(4*k+3)) % 33 ≠ 7 := by
  omega

#print axioms pow_mod_period
#print axioms no_b1
#print axioms no_b2
#print axioms no_b3
#print axioms no_b4
end Agent22Special
