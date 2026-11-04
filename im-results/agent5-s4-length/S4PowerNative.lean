import S4NativeValuation
import S4PowerBridge

namespace S4NativeCompact

/-- Exact all-input halting gate of the original source's 27-epoch S4
    compact return, with the original unchanged Cryptids stepEpoch imported. -/
theorem nativeReduced_none_iff_pow2 (T : List Nat) :
    nativeReduced T = none ↔ ∃ k : Nat, _root_.W T + 45 = 2^k := by
  rw [nativeReduced_eq_compactNext]
  rw [← S4Length.F_eq_original T]
  rw [← S4Power.F_eq_source T]
  rw [S4Power.F_none_iff_pow2]
  simp only [S4Power.Pow2]
  rw [S4Power.W_eq_source, S4Length.W_eq_original]

#print axioms nativeReduced_none_iff_pow2
end S4NativeCompact
