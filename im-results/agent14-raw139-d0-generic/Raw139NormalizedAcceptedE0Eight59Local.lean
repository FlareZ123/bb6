import Raw139NormalizedAcceptedE0OneRF60Local
import Raw139NormalizedAcceptedE0Seven60Local

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedAcceptedE0Eight59Local

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite
open BB6.Agent14Raw139NormalizedE0OneRFCuts
open BB6.Agent14Raw139AcceptedE0SixCover
open BB6.Agent14Raw139NormalizedAcceptedE0OneRF60Local

/-- Eight distinct, original-source normalized E0 parent Covers.
    The eighth requires the source-certified ZeroLF 3862 discharge. -/
theorem acceptedEight_cover :
    ∀ q ∈ acceptedEight, Cover (WeightedBound e0Score) q := by
  intro q hq
  simp only [acceptedEight, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact BB6.Agent14Raw139NormalizedAcceptedE0Seven60Local.e0ZeroLF_cover
  · exact acceptedSixPlusOneRF_cover q hq

/-- Raw139's local parent Cover follows from exactly 59 explicit normalized
    residual table Covers. It does not close those residuals or BB(6). -/
theorem raw139_p0_cover_from_59_eight_accepted
    (hNorm : ∀ p ∈ normalizedAfterEight,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_p0_cover_from_59_eight
    (by
      intro q hq
      exact BB6.Agent14Raw139AcceptedE0SixCover.cover_mono
        (by simpa [e0Score] using localScore_ge_6766859)
        (acceptedEight_cover q hq))
    hNorm

#print axioms acceptedEight_cover
#print axioms raw139_p0_cover_from_59_eight_accepted

end BB6.Agent14Raw139NormalizedAcceptedE0Eight59Local
