import Mathlib

namespace BB6.Agent20AdjacentEven

/-- For any integer affine scale, the denominator of its adjacent valuation
    divides the signed difference of even powers. -/
theorem adjacent_even_power (L k : Nat) (hk : Even k) :
    ((2*L+3 : Nat) : Int) ∣
      (((L+3 : Nat) : Int)^k - (L : Int)^k) := by
  have h := sub_dvd_pow_sub_pow
    (((L+3 : Nat) : Int)) (-(L : Int)) k
  have hbase :
      (((L+3 : Nat) : Int)) - (-(L : Int)) =
      ((2*L+3 : Nat) : Int) := by
    push_cast
    ring
  rw [hbase] at h
  have hneg : (-(L : Int))^k = (L : Int)^k := hk.neg_pow _
  simpa only [hneg] using h

/-- Universal parity resonance, including valuations zero and one. -/
theorem adjacent_even_gap (v k : Nat) (hk : Even k) :
    ((2^(v+2)+3 : Nat) : Int) ∣
      (((2^(v+1)+3 : Nat) : Int)^k -
       ((2^(v+1) : Nat) : Int)^k) := by
  have h := adjacent_even_power (2^(v+1)) k hk
  have heq : 2^(v+2)+3 = 2*(2^(v+1))+3 := by
    rw [pow_succ]
    ring
  simpa only [heq] using h

#print axioms adjacent_even_power
#print axioms adjacent_even_gap
end BB6.Agent20AdjacentEven
