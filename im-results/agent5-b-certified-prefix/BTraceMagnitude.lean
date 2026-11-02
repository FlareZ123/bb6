import BTraceSource
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 150000

namespace BB6.BTrace

/-- The verified third iterate has exactly 132847 bits. -/
theorem third_sample_bits :
    2^132846 ≤ iterG 227097 0 ∧ iterG 227097 0 < 2^132847 := by
  rw [prefix28]
  constructor <;> decide

/-- The next synthetic reset has over 132846 bits of magnitude. -/
theorem fourth_reset_lower : 2^132846 ≤ BB6.OneDim.scalarA 3 := by
  have h := third_sample_bits.1
  rw [←source_iterG_eq, ←source_scalarA_2] at h
  have hs := source_sample2
  have ha : BB6.OneDim.scalarA 3 = BB6.OneDim.iterG (BB6.OneDim.scalarA 2) 0 + 6 := by
    rw [BB6.OneDim.scalarA]
    omega
  omega

#print axioms third_sample_bits
#print axioms fourth_reset_lower
end BB6.BTrace
