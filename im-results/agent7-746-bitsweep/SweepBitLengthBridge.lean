import ScanFail
import SweepBitLength

namespace CascadeFastReturn

/-- Extensional agreement with the already source-proved first-failed scanner. -/
theorem firstFailedK_eq_bit (h : Nat) :
    firstFailedK h = CascadeBitSweep.firstFailIndex h := by
  apply (CascadeBitSweep.firstFailIndex_unique h (firstFailedK h)
    (firstFailedK_spec h).1 ?_).symm
  intro j hj
  have hh := (firstFailedK_spec h).2 j hj
  change ¬(h + j + 5 < 8 * 2 ^ j) at hh
  omega

#print axioms firstFailedK_eq_bit

end CascadeFastReturn
