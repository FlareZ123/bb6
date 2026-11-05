import Lean

namespace BB6.Agent45Exception

private theorem power_ge_exponent (e t : Nat)
    (h : 2^e ≤ 2^t) : e ≤ t := by
  by_cases hle : e ≤ t
  · exact hle
  have ht : t+1 ≤ e := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) ht
  have hstep : 2^(t+1) = 2^t*2 := by rw [Nat.pow_succ]
  rw [hstep] at hp
  have hpos : 0 < 2^t := by exact Nat.two_pow_pos t
  omega

theorem no_power_low_offset
    (e s z t : Nat)
    (hz : 0 < z)
    (hsmall : 2*z < 2^e)
    (hsize : 2^e ≤ s)
    (hcong : 2^e ∣ s+2*z)
    (hpow : s = 2^t) : False := by
  have htle : e≤t := power_ge_exponent e t (hpow ▸ hsize)
  have hdiv : 2^e ∣ s := by
    rw [hpow]
    exact Nat.pow_dvd_pow 2 htle
  have hzdiv : 2^e ∣ 2*z := by
    have h := Nat.dvd_sub hcong hdiv
    simpa only [Nat.add_sub_cancel_left] using h
  have hpositive : 0 < 2*z := by omega
  have hbound : 2^e ≤ 2*z := Nat.le_of_dvd hpositive hzdiv
  omega

#print axioms power_ge_exponent
#print axioms no_power_low_offset

end BB6.Agent45Exception
