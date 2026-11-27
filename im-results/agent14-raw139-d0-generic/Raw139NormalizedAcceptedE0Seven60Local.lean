import Raw139NormalizedAcceptedE0Six61Local
import E0ZeroLFDischarge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedAcceptedE0Seven60Local

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0Cuts
open BB6.Agent14Raw139AcceptedE0SixCover

/-- The seventh accepted E0 table is *exactly* the certified physical ZeroLF parent. -/
theorem e0ZeroLF_eq_parent :
    e0ZeroLF = BB6.Agent14E0LFParent.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

/-- Source ZeroLF Cover transported without losing its exact local score. -/
theorem e0ZeroLF_cover :
    Cover (WeightedBound e0Score) e0ZeroLF := by
  rw [e0ZeroLF_eq_parent]
  exact BB6.Agent14Raw139AcceptedE0SixCover.cover_mono
    (by decide : 19007 ≤ e0Score)
    BB6.Agent14E0LFParent.weighted

/-- Every removed normalized E0 cylinder has an actual source Cover. -/
theorem acceptedE0Seven_cover :
    ∀ q ∈ acceptedE0Seven, Cover (WeightedBound e0Score) q := by
  intro q hq
  simp only [acceptedE0Seven, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | hq
  · exact e0ZeroLF_cover
  · exact BB6.Agent14Raw139AcceptedE0SixCover.acceptedE0Six_cover q hq

/-- Fully source-certified seven-parent Raw139 reduction, leaving exactly
    sixty explicit normalized table Cover hypotheses, no new parent premises. -/
theorem raw139_p0_cover_from_60_accepted
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Seven,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_p0_cover_from_60
    (by
      intro q hq
      exact BB6.Agent14Raw139NormalizedAcceptedE0Six61Local.cover_mono
        (by simpa [e0Score] using localScore_ge_6766859)
        (acceptedE0Seven_cover q hq))
    hNorm

#print axioms e0ZeroLF_eq_parent
#print axioms e0ZeroLF_cover
#print axioms acceptedE0Seven_cover
#print axioms raw139_p0_cover_from_60_accepted

end BB6.Agent14Raw139NormalizedAcceptedE0Seven60Local
