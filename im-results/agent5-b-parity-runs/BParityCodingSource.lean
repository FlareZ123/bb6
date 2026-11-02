import BParityCoding
import BParityRunsSource

namespace BB6.BParityRuns

/-- Exact 2-adic first differing parity time for the unchanged original B map. -/
theorem source_parity_gap (k z m : Nat) (hm : m%2=1) :
    OneDim.iterG k (z+2^k*m) = OneDim.iterG k z + 3^k*m ∧
    (∀ j < k, OneDim.iterG j (z+2^k*m)%2 = OneDim.iterG j z%2) ∧
    OneDim.iterG k (z+2^k*m)%2 ≠ OneDim.iterG k z%2 := by
  simpa only [source_iterG] using G_parity_gap k z m hm

/-- The authentic Machine B scalar parity sequence is not eventually periodic. -/
theorem source_no_eventual_parity_period (z start p : Nat) (hp : 0<p) :
    ¬ ∀ k : Nat, OneDim.iterG (start+k) z%2 =
      OneDim.iterG (start+k+p) z%2 := by
  simpa only [source_iterG] using G_no_eventual_parity_period z start p hp

#print axioms source_parity_gap
#print axioms source_no_eventual_parity_period
#print axioms source_later_opposite
end BB6.BParityRuns
