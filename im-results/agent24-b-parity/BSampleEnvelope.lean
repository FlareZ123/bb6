import BResetResidues
import BParityDiscrepancy

namespace BB6.Agent24.SampleEnvelope
open BB6.Agent24
open BB6.Agent24.Reset
open BB6.Agent24.Discrepancy

/-- Exact source-independent exponential envelope for every sampled scalar value. -/
theorem all_sample_values_scaled (n : Nat) :
    8*3^(resetA n) ≤ 2^(resetA n)*(sampleZ n+8) ∧
    2^(resetA n)*(sampleZ n+15) ≤ 15*3^(resetA n) := by
  have hlow := scaled_orbit_lower (resetA n)
  have hhigh := scaled_orbit_upper (resetA n)
  rw [orbit_shift,gOrbit_eq_iterG] at hlow hhigh
  have he : iterG (resetA n) 0 + 8 + 7 = iterG (resetA n) 0 + 15 := by omega
  rw [he] at hhigh
  exact ⟨hlow,hhigh⟩

/-- Next reset is at most three away from the sampled scalar orbit value plus nine. -/
theorem next_reset_scaled_bounds (n : Nat) :
    (sampleZ n+6 ≤ resetA (n+1)) ∧
    (resetA (n+1) ≤ sampleZ n+9) := by
  have hb := Nat.mod_lt (sampleZ n) (by omega : 0<2)
  dsimp [resetA, sampleZ] at *
  omega

/-- Direct, uniform two-sided growth bounds for the recursively sampled reset indices. -/
theorem all_reset_index_growth (n : Nat) :
    8*3^(resetA n) ≤ 2^(resetA n)*(resetA (n+1)+2) ∧
    2^(resetA n)*(resetA (n+1)+6) ≤ 15*3^(resetA n) := by
  have hs := all_sample_values_scaled n
  have hnext := next_reset_scaled_bounds n
  have hlo : sampleZ n+8 ≤ resetA (n+1)+2 := by omega
  have hhi : resetA (n+1)+6 ≤ sampleZ n+15 := by omega
  constructor
  · exact Nat.le_trans hs.1 (Nat.mul_le_mul_left _ hlo)
  · exact Nat.le_trans (Nat.mul_le_mul_left _ hhi) hs.2

#print axioms all_reset_index_growth

#print axioms all_sample_values_scaled
#print axioms next_reset_scaled_bounds
end BB6.Agent24.SampleEnvelope
