import Raw139NormalizedE0OneRFCuts
import Raw139AcceptedE0SixCover
import E0OneRFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedAcceptedE0OneRF60Local

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite
open BB6.Agent14Raw139NormalizedE0OneRFCuts
open BB6.Agent14Raw139AcceptedE0SixCover

/-- Exact physical-table transport: 1RF is a genuine normalized Raw139 E0 row. -/
theorem e0OneRF_eq_parent :
    e0OneRF = BB6.Agent6E0OneRF.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

/-- Accepted E0=1RF original-source weighted bound, lifted to the local floor. -/
theorem e0OneRF_cover :
    Cover (WeightedBound e0Score) e0OneRF := by
  rw [e0OneRF_eq_parent]
  exact BB6.Agent14Raw139AcceptedE0SixCover.cover_mono
    (by decide : 6024 ≤ e0Score)
    BB6.Agent6E0OneRF.weighted

theorem acceptedSixPlusOneRF_cover :
    ∀ q ∈ acceptedSixPlusOneRF, Cover (WeightedBound e0Score) q := by
  intro q hq
  simp only [acceptedSixPlusOneRF, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact e0OneRF_cover
  · exact acceptedE0Six_cover q hq

/-- There are exactly sixty remaining normalized Raw139 Cover hypotheses.
    All seven eliminated source-parent Covers are supplied, not assumed. -/
theorem raw139_p0_cover_from_60_oneRF_accepted
    (hNorm : ∀ p ∈ normalizedAfterSixPlusOneRF,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_p0_cover_from_60_oneRF
    (by
      intro q hq
      exact BB6.Agent14Raw139AcceptedE0SixCover.cover_mono
        (by simpa [e0Score] using localScore_ge_6766859)
        (acceptedSixPlusOneRF_cover q hq))
    hNorm

#print axioms e0OneRF_eq_parent
#print axioms e0OneRF_cover
#print axioms acceptedSixPlusOneRF_cover
#print axioms raw139_p0_cover_from_60_oneRF_accepted

end BB6.Agent14Raw139NormalizedAcceptedE0OneRF60Local
