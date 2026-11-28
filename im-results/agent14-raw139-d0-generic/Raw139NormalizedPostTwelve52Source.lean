import Raw139NormalizedPostTwelve52
import Raw139NormalizedPostTwelve53Source
import E0OneLFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve52Source

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve53Source
open BB6.Agent14Raw139NormalizedPostTwelve52

theorem oneLF_exact :
    e0OneLF = BB6.Agent6E0OneLF.parent := by
  exact sameTable_sound (by decide)

/-- The newly recovered E0=1LF whole-parent theorem is lifted from its native
    source-certified cutoff 90,794 to any larger weighted bound. -/
theorem source_oneLF_cover (B : Nat) (hb : 90794 ≤ B) :
    Cover (WeightedBound B) e0OneLF := by
  rw [oneLF_exact]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent6E0OneLF.weighted.sound m hm k d hk hd) hb

/-- Direct source-grafted original Raw139 p0 interface after the twelve E0
    cuts plus C1=1LC, F1=0LD, and the newly certified E0=1LF cylinder:
    only the exact 52-table normalized complement and unchanged spine
    obligations remain. -/
theorem raw139_p0_cover_from_52_source (B : Nat)
    (hb : 90794 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h52 : ∀ p ∈ normalizedAfterTwelvePlusThree,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_52 B
    (Nat.le_trans (by decide : 59 ≤ 90794) hb)
    ha hTwelve
    (sourceAcceptedExtraTwo_cover B
      (Nat.le_trans (by decide : 598 ≤ 90794) hb))
    (source_oneLF_cover B hb)
    h52 hrc hre hf

#print axioms oneLF_exact
#print axioms source_oneLF_cover
#print axioms raw139_p0_cover_from_52_source

end BB6.Agent14Raw139NormalizedPostTwelve52Source
