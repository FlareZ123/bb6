import T0EvenParentArithmetic
import T0EvenParentPowerBounds

namespace Agent10T0Parent

/--
The source-band form of the t=0 even-entry exclusion. The only remaining
inputs are the exact t=0 fatal equation, the entry deficit scaling
delta = 2^q * e, and the source-band lower bound on the fatal-tail depth.
The power inequalities are derived by t0_entry_even_parent_power_bounds.
-/
theorem t0_entry_even_parent_no_solution_of_source_band
    (K q r delta e : Nat)
    (hK : 266 ≤ K)
    (hq : q ≤ K - 1)
    (hdelta_lo : K + 3 ≤ delta)
    (hdelta_hi : delta ≤ 2 * K + 4)
    (he_pos : 0 < e)
    (he : delta = 2 ^ q * e)
    (hband_r :
      8 * 2 ^ K + (2 * K + 7) + 3 ≤ (2 * K + 7) * 2 ^ (r + 2))
    (heq :
      (2 * K + 7) * 2 ^ (q + r + 3) + 2 ^ q * (2 * K + 1) =
        2 ^ (K + q + 4) + 12 * 2 ^ K + 3 * delta) : False := by
  have hpow := t0_entry_even_parent_power_bounds K q r e delta
    (by omega) hq he_pos he hdelta_hi hband_r
  exact t0_entry_even_parent_arithmetic_no_solution K q r delta
    hK hq hdelta_lo hdelta_hi hpow.1 hpow.2 heq

#print axioms t0_entry_even_parent_no_solution_of_source_band

end Agent10T0Parent
