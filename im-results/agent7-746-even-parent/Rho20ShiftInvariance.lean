import Rho20Class2Arithmetic
import Rho20Phase143246Arithmetic

namespace Agent7Rho20Shift

/-- Adding a multiple of 486 preserves the phase modulo 54. -/
theorem add486_mod54 (x m : Nat) :
    (x + 486*m) % 54 = x % 54 := by
  have hm : (486*m) % 54 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨9*m, by omega⟩
  rw [Nat.add_mod, hm]
  simp

/-- Adding a multiple of 486 preserves the phase modulo 162. -/
theorem add486_mod162 (x m : Nat) :
    (x + 486*m) % 162 = x % 162 := by
  have hm : (486*m) % 162 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨3*m, by omega⟩
  rw [Nat.add_mod, hm]
  simp

/-- Adding a multiple of 486 preserves residues modulo 243. -/
theorem add486_mod243 (x m : Nat) :
    (x + 486*m) % 243 = x % 243 := by
  have hm : (486*m) % 243 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨2*m, by omega⟩
  rw [Nat.add_mod, hm]
  simp

/-- Adding a multiple of 972 preserves residues modulo 243. -/
theorem add972_mod243 (x m : Nat) :
    (x + 972*m) % 243 = x % 243 := by
  have hm : (972*m) % 243 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨4*m, by omega⟩
  rw [Nat.add_mod, hm]
  simp

/-- The period-162 power law makes the 486-shift invisible modulo 243. -/
theorem pow2_mod243_shift (e m : Nat) :
    2^(e + 486*m) % 243 = 2^e % 243 := by
  have hexp : e + 486*m = e + 162*(3*m) := by omega
  rw [hexp]
  exact Agent7Rho20.pow2_mod243_period e (3*m)

/-- The q exponent is invariant under a 486-shift of K. -/
theorem q_mod243_shift (k a m : Nat) (ha : a ≤ k) :
    2^(k + 486*m - a) % 243 = 2^(k-a) % 243 := by
  have hexp : k + 486*m - a = (k-a) + 486*m := by omega
  rw [hexp]
  exact pow2_mod243_shift (k-a) m

/-- The r exponent is invariant under a 486-shift of K. -/
theorem r_mod243_shift (k a m : Nat) (ha : a ≤ k) :
    2^(k + 486*m + 4 - a) % 243 = 2^(k+4-a) % 243 := by
  have hexp : k + 486*m + 4 - a = (k+4-a) + 486*m := by omega
  rw [hexp]
  exact pow2_mod243_shift (k+4-a) m

/-- The coefficient 2K+7 is invariant modulo 243 under K -> K+486m. -/
theorem twokplus7_mod243_shift (k m : Nat) :
    (2*(k + 486*m) + 7) % 243 = (2*k + 7) % 243 := by
  have heq : 2*(k + 486*m) + 7 = (2*k+7) + 972*m := by omega
  rw [heq]
  exact add972_mod243 (2*k+7) m

/-- The full B=(2K+7)2^(K+4-a) residue is invariant under the shift. -/
theorem B_mod243_shift (k a m : Nat) (ha : a ≤ k) :
    ((2*(k + 486*m) + 7) * 2^(k + 486*m + 4 - a)) % 243 =
    ((2*k + 7) * 2^(k+4-a)) % 243 := by
  calc
    ((2*(k + 486*m) + 7) * 2^(k + 486*m + 4 - a)) % 243
        = (((2*(k + 486*m) + 7) % 243) *
           (2^(k + 486*m + 4 - a) % 243)) % 243 := by
             rw [Nat.mul_mod]
    _ = (((2*k + 7) % 243) * (2^(k+4-a) % 243)) % 243 := by
          rw [twokplus7_mod243_shift, r_mod243_shift k a m ha]
    _ = ((2*k + 7) * 2^(k+4-a)) % 243 := by
          rw [Nat.mul_mod]

/-- The shifted g coefficient is unchanged modulo 243. -/
theorem g_mod243_shift (g m : Nat) :
    (g + 972*m) % 243 = g % 243 :=
  add972_mod243 g m

/-- The rho-20 congruence is preserved by the same K shift. -/
theorem rho20_shift_mod54 (k a m : Nat) :
    (k + 486*m + 6*a) % 54 = (k + 6*a) % 54 := by
  have heq : k + 486*m + 6*a = (k+6*a) + 486*m := by omega
  rw [heq]
  exact add486_mod54 (k+6*a) m

theorem phase14_k_shift_mod162 (n m : Nat) :
    (Agent10Rho20Phase143246.k14 n + 486*m) % 162 = 152 := by
  calc
    (Agent10Rho20Phase143246.k14 n + 486*m) % 162
        = Agent10Rho20Phase143246.k14 n % 162 := add486_mod162 _ _
    _ = 152 := Agent10Rho20Phase143246.k14_mod162 n

theorem phase32_k_shift_mod162 (n m : Nat) :
    (Agent10Rho20Phase143246.k32 n + 486*m) % 162 = 44 := by
  calc
    (Agent10Rho20Phase143246.k32 n + 486*m) % 162
        = Agent10Rho20Phase143246.k32 n % 162 := add486_mod162 _ _
    _ = 44 := Agent10Rho20Phase143246.k32_mod162 n

theorem phase46_k_shift_mod162 (n m : Nat) :
    (Agent10Rho20Phase143246.k46 n + 486*m) % 162 = 122 := by
  calc
    (Agent10Rho20Phase143246.k46 n + 486*m) % 162
        = Agent10Rho20Phase143246.k46 n % 162 := add486_mod162 _ _
    _ = 122 := Agent10Rho20Phase143246.k46_mod162 n

theorem phase38_k_shift_mod162 (n m : Nat) :
    (Agent7Rho20.kParam n + 486*m) % 162 = 116 := by
  calc
    (Agent7Rho20.kParam n + 486*m) % 162
        = Agent7Rho20.kParam n % 162 := add486_mod162 _ _
    _ = 116 := Agent7Rho20.k_mod162 n

theorem phase14_p_shift_mod243 (n m : Nat) :
    2^(Agent10Rho20Phase143246.k14 n + 486*m) % 243 = 229 := by
  calc
    2^(Agent10Rho20Phase143246.k14 n + 486*m) % 243
        = 2^(Agent10Rho20Phase143246.k14 n) % 243 := pow2_mod243_shift _ _
    _ = 229 := Agent10Rho20Phase143246.p14_mod243 n

theorem phase32_p_shift_mod243 (n m : Nat) :
    2^(Agent10Rho20Phase143246.k32 n + 486*m) % 243 = 67 := by
  calc
    2^(Agent10Rho20Phase143246.k32 n + 486*m) % 243
        = 2^(Agent10Rho20Phase143246.k32 n) % 243 := pow2_mod243_shift _ _
    _ = 67 := Agent10Rho20Phase143246.p32_mod243 n

theorem phase46_p_shift_mod243 (n m : Nat) :
    2^(Agent10Rho20Phase143246.k46 n + 486*m) % 243 = 22 := by
  calc
    2^(Agent10Rho20Phase143246.k46 n + 486*m) % 243
        = 2^(Agent10Rho20Phase143246.k46 n) % 243 := pow2_mod243_shift _ _
    _ = 22 := Agent10Rho20Phase143246.p46_mod243 n

theorem phase38_p_shift_mod243 (n m : Nat) :
    2^(Agent7Rho20.kParam n + 486*m) % 243 = 175 := by
  calc
    2^(Agent7Rho20.kParam n + 486*m) % 243
        = 2^(Agent7Rho20.kParam n) % 243 := pow2_mod243_shift _ _
    _ = 175 := Agent7Rho20.p_mod243 n

end Agent7Rho20Shift
