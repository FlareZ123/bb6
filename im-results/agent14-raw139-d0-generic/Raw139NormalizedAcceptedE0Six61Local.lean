import Raw139NormalizedE0Cuts
import Raw139AcceptedE0SixCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedAcceptedE0Six61Local

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0Cuts
open BB6.Agent14Raw139AcceptedE0SixCover

theorem cover_mono {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  cases h with
  | leaf _ hbound =>
      refine Cover.leaf _ ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB

/-- Unconditional use of all six currently source-accepted normalized E0
    parents. Only the 61 explicit normalized residual-table Covers remain. -/
theorem raw139_p0_cover_from_61_accepted
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Six,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_p0_cover_from_61
    (by
      intro q hq
      exact cover_mono
        (by simpa [e0Score] using localScore_ge_6766859)
        (acceptedE0Six_cover q hq))
    hNorm

#print axioms cover_mono
#print axioms raw139_p0_cover_from_61_accepted

end BB6.Agent14Raw139NormalizedAcceptedE0Six61Local
