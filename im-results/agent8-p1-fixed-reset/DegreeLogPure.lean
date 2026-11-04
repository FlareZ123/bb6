import Std
namespace BB6.Agent8Log

/-- An e-th-power upper bound on a dyadic exponential forces a
quantified logarithmic lower bound on the polynomial exponent. -/
theorem power_log_degree_bound (n b e : Nat) (he : 0 < e)
    (hbound : 2^n ≤ b^e) :
    n < (b.log2+1)*e := by
  let L := b.log2+1
  have hbase : b < 2^L := by
    simpa only [L] using (Nat.lt_log2_self (n:=b))
  have hpowUpper : b^e < 2^(L*e) := by
    rw [Nat.pow_mul]
    exact Nat.pow_lt_pow_left hbase (by omega)
  have hboth : 2^n < 2^(L*e) := by omega
  by_cases hmain : n < L*e
  · exact hmain
  · have hnot : L*e ≤ n := by omega
    have hpowMon : (2:Nat)^(L*e) ≤ 2^n := Nat.pow_le_pow_right (by decide) hnot
    omega

#print axioms power_log_degree_bound
end BB6.Agent8Log
