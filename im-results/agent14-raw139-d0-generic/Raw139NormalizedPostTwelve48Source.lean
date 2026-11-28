import Raw139NormalizedPostTwelve48
import Raw139NormalizedPostTwelve49Source
import E0ZeroLCCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve48Source

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve48
open BB6.Agent14Raw139NormalizedPostTwelve49Source

theorem zeroLC_exact :
    e0ZeroLC = BB6.Agent6E0ZeroLCExact.parent := by
  exact sameTable_sound (by decide)

theorem source_e0ZeroLC_cover (B : Nat) (hb : 80377 ≤ B) :
    Cover (WeightedBound B) e0ZeroLC := by
  rw [zeroLC_exact]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent6E0ZeroLCExact.weighted.sound m hm k d hk hd) hb

/-- Source-grafted Raw139 p0 interface after the accepted full E0=0LC
    cylinder is removed.  At common cutoff 881,057, only the exact 48-row
    normalized complement, the twelve prospective E0-family premise, and
    the unchanged spine obligations remain. -/
theorem raw139_p0_cover_from_48_source (B : Nat)
    (hb : 881057 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h48 : ∀ p ∈ normalizedAfterTwelvePlusSeven,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_49_source B hb ha hTwelve
    (normalized49_cover_from_48 B
      (source_e0ZeroLC_cover B
        (Nat.le_trans (by decide : 80377 ≤ 881057) hb))
      h48)
    hrc hre hf

#print axioms zeroLC_exact
#print axioms source_e0ZeroLC_cover
#print axioms raw139_p0_cover_from_48_source

end BB6.Agent14Raw139NormalizedPostTwelve48Source
