import Lean
namespace BB6.Shadow

/-- A genuine inverse input with right coordinate one forces an exact power
of two, incompatible with a nonzero small binary carry from the shadow offset. -/
theorem no_one_after_binary_gap (J t s z : Nat)
    (hz : 0 < z)
    (hzsmall : 2*z < 2^J)
    (hdiv : 2^J ∣ s+2*z)
    (hpower : s=2^t*(1+3))
    (hlarge : 2^J < s) : False := by
  have hs : s=2^(t+2) := by
    calc
      s = 2^t*4 := by simpa using hpower
      _ = 2^(t+2) := by simp [Nat.pow_add]
  have ht : J ≤ t+2 := by
    by_cases h : J ≤ t+2
    · exact h
    · have hb : t+2 ≤ J := by omega
      have hp : 2^(t+2) ≤ 2^J := Nat.pow_le_pow_right (by decide) hb
      omega
  have hsd : 2^J ∣ s := by
    rw [hs]
    exact Nat.pow_dvd_pow 2 ht
  have hzd : 2^J ∣ 2*z := by
    have hsub := Nat.dvd_sub hdiv hsd
    have heq : s+2*z-s=2*z := by omega
    simpa only [heq] using hsub
  have hsmall : 2^J ≤ 2*z := Nat.le_of_dvd (by omega) hzd
  omega

/-- A bounded-cost original feeder has shifted right coordinate exceeding
    the full dyadic scale, provided its mass is the prescribed 56-power. -/
theorem shifted_gt_power (N L m b d : Nat)
    (hmass : b+d+2*m+2*L+3=56*2^N)
    (hsmall : m+L≤2^N)
    (hb : b%2=0) : 2^N < d+b/2+3 := by
  have hbhalf : b=2*(b/2) := by omega
  omega

#print axioms shifted_gt_power
#print axioms no_one_after_binary_gap
end BB6.Shadow
