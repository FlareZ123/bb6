import BBlockAffine
import BParityRunsSource

namespace BB6.BParityRuns

/-- The pinned original Machine B two-branch scalar model admits a
    complete 2^k-branch affine block acceleration for every k. -/
theorem source_block_split (k z : Nat) :
    OneDim.iterG k z =
      OneDim.iterG k (z%2^k) +3^k*(z/2^k) := by
  simpa only [source_iterG] using G_block_split k z

#print axioms source_block_split
end BB6.BParityRuns
