import Raw139NormalizedPostTwelve49
import Raw139NormalizedPostTwelve50Source
import Raw139E0OneLACover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve49Source

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve49
open BB6.Agent14Raw139NormalizedPostTwelve50Source

theorem oneLA_exact :
    e0OneLA =
      BB6Coverage.FAR.fromCodes [7,24,11,24,14,24,24,16,2,11,24,24] := by
  exact sameTable_sound (by decide)

theorem source_oneLA_cover (B : Nat) (hb : 881057 ≤ B) :
    Cover (WeightedBound B) e0OneLA := by
  rw [oneLA_exact]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent48Raw139E0OneLA.all_completions_weighted m hm k d hk hd)
    hb

/-- Source-grafted Raw139 p0 interface after E0=1LA is removed.  At common
    cutoff 881,057 only the exact 49-row complement, the twelve prospective
    E0-family premise, and the unchanged spine obligations remain. -/
theorem raw139_p0_cover_from_49_source (B : Nat)
    (hb : 881057 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h49 : ∀ p ∈ normalizedAfterTwelvePlusSix,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_50_source B
    (Nat.le_trans (by decide : 90794 ≤ 881057) hb)
    ha hTwelve
    (normalized50_cover_from_49 B (source_oneLA_cover B hb) h49)
    hrc hre hf

#print axioms oneLA_exact
#print axioms source_oneLA_cover
#print axioms raw139_p0_cover_from_49_source

end BB6.Agent14Raw139NormalizedPostTwelve49Source
