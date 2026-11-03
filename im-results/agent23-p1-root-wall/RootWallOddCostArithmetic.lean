import CriticalRootWallArithmetic

namespace BB6.Agent23RootWall

/-- Every reset seed on the low-cost critical-root wall lies strictly
    between successive 14-times-powers-of-two. -/
theorem no_low_wall_reset_power (n m r z : Nat)
    (hn : 4 ≤ n) (hm : m < 2^n)
    (hbalance : r+4*n+2*m+16 = 14*2^n)
    (hreset : r+8 = 14*2^z) : False := by
  have hgrowth := exp_growth n hn
  have hhalf : 2^n=2*2^(n-1) := by
    have hnval : n=(n-1)+1 := by omega
    calc
      2^n = 2^((n-1)+1) := by congr 1
      _ = 2*2^(n-1) := by rw [Nat.pow_succ]; omega
  have hlo : 7*2^n < r+8 := by omega
  have hhi : r+8 < 14*2^n := by omega
  by_cases hzlt : z < n
  · have hle : z ≤ n-1 := by omega
    have hpow : 2^z ≤ 2^(n-1) := Nat.pow_le_pow_right (by decide) hle
    omega
  · have hle : n ≤ z := by omega
    have hpow : 2^n ≤ 2^z := Nat.pow_le_pow_right (by decide) hle
    omega

#print axioms no_low_wall_reset_power
end BB6.Agent23RootWall
