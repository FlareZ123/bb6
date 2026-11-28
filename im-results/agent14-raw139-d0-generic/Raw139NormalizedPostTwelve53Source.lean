import Raw139NormalizedPostTwelve53
import C1OneLCParent
import ChampionF1ZeroLDCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve53Source

open BB6Coverage
open BB6Coverage.FAR
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53

theorem oneLC_exact :
    leaf (4, ⟨true, false, 2⟩) =
      BB6Coverage.FAR.fromCodes [7,24,11,24,14,10,3,16,12,11,24,24] := by
  exact sameTable_sound (by decide)

theorem zeroLD_exact :
    leaf (5, ⟨false, false, 3⟩) =
      BB6.Agent48F1ZeroLD.parent := by
  exact sameTable_sound (by decide)

/-- Direct source Covers for the two exact rows eliminated by the 55→53
    finite reduction.  Both accepted native bounds are below 598. -/
theorem sourceAcceptedExtraTwo_cover (B : Nat) (hb : 598 ≤ B) :
    ∀ q ∈ sourceAcceptedExtraTwo, Cover (WeightedBound B) q := by
  intro q hq
  simp only [sourceAcceptedExtraTwo, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl | rfl
  · rw [oneLC_exact]
    exact BB6.Agent6C1OneLCParent.cover_oneLC B hb
  · rw [zeroLD_exact]
    apply Cover.leaf
    intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent48F1ZeroLD.all_completions_weighted m hm k d hk hd)
      (Nat.le_trans (by decide : 124 ≤ 598) hb)

/-- Source-grafted Raw139 p0 interface: the independently accepted C1=1LC
    and F1=0LD cylinders are no longer premises.  Twelve E0 parent Covers,
    the exact 53-row complement, and the unchanged spine obligations suffice. -/
theorem raw139_p0_cover_from_53_source_extra (B : Nat)
    (hb : 598 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h53 : ∀ p ∈ normalizedAfterTwelvePlusTwo,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_53 B
    (Nat.le_trans (by decide : 59 ≤ 598) hb)
    ha hTwelve (sourceAcceptedExtraTwo_cover B hb) h53 hrc hre hf

#print axioms oneLC_exact
#print axioms zeroLD_exact
#print axioms sourceAcceptedExtraTwo_cover
#print axioms raw139_p0_cover_from_53_source_extra

end BB6.Agent14Raw139NormalizedPostTwelve53Source
