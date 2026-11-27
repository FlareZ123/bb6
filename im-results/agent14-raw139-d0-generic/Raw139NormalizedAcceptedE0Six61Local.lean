import Raw139NormalizedE0Cuts
import Raw139AcceptedE0SixCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedAcceptedE0Six61Local

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6Raw139Normalized
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0Cuts
open BB6.Agent14Raw139AcceptedE0SixCover

/-- Unconditional use of all six currently source-accepted normalized E0
    parents. Only the 61 explicit normalized residual-table Covers remain. -/
theorem raw139_p0_cover_from_61_accepted
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Six,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_p0_cover_from_61 acceptedE0Six_cover hNorm

#print axioms raw139_p0_cover_from_61_accepted

end BB6.Agent14Raw139NormalizedAcceptedE0Six61Local
