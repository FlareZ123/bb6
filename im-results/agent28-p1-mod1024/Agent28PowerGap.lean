import Std

namespace BB6.Agent28

/-- For any power of two X=2^n, an integer strictly between 7X and 14X
cannot equal 14 times a power of two. -/
theorem no_power_between (n p j : Nat)
    (hl : 7*2^n < p) (hu : p < 14*2^n) :
    p ≠ 14*2^j := by
  intro heq
  by_cases h : j<n
  · have hle : (2:Nat)^(j+1) ≤ 2^n :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hle
    omega
  · have hle : (2:Nat)^n ≤ 2^j :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

end BB6.Agent28
