import Raw139NormalizedPostTwelve51
import Raw139NormalizedPostTwelve52Source
import C1ZeroLAParent

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve51Source

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve52
open BB6.Agent14Raw139NormalizedPostTwelve52Source
open BB6.Agent14Raw139NormalizedPostTwelve51

theorem zeroLA_exact :
    c1ZeroLA =
      BB6Coverage.FAR.fromCodes [7,24,11,24,14,0,3,16,12,11,24,24] := by
  exact sameTable_sound (by decide)

theorem source_zeroLA_cover (B : Nat) (hb : 266 ≤ B) :
    Cover (WeightedBound B) c1ZeroLA := by
  rw [zeroLA_exact]
  exact BB6.Agent6C1ZeroLAParent.cover_zeroLA B hb

/-- Direct source-grafted Raw139 p0 interface after the accepted C1=0LA
    whole cylinder is removed as well.  At the common cutoff 90,794,
    only the exact 51-row complement plus the twelve-E0 and unchanged
    spine premises remain. -/
theorem raw139_p0_cover_from_51_source (B : Nat)
    (hb : 90794 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h51 : ∀ p ∈ normalizedAfterTwelvePlusFour,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_52_source B hb ha hTwelve
    (normalized52_cover_from_51 B
      (source_zeroLA_cover B
        (Nat.le_trans (by decide : 266 ≤ 90794) hb))
      h51)
    hrc hre hf

#print axioms zeroLA_exact
#print axioms source_zeroLA_cover
#print axioms raw139_p0_cover_from_51_source

end BB6.Agent14Raw139NormalizedPostTwelve51Source
