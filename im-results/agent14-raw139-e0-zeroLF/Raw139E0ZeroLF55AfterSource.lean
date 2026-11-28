import Raw139NormalizedE0ElevenCertifiedConditional
import E0ZeroLFDischarge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139E0ZeroLF55AfterSource

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedConditional

/-- The recovered source-certified ZeroLF parent is exactly the normalized
    E0=0LF physical table occurring in the Raw139 residual family. -/
theorem zeroLF_is_exact_normalized_E0 :
    e0ZeroLF = BB6.Agent14E0LFParent.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

/-- Lift an already verified weighted Cover to any larger cutoff by semantic
    soundness.  Rebuilding a leaf is enough: the source Cover's internal
    partition is irrelevant once all compatible machines are known bounded. -/
theorem monotone_cover {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (h.sound m hm k d hk hd) hAB

/-- Unconditional normalized ZeroLF Cover after the exact exceptional 3862
    source proof has been joined to the conditional six-hole parent. -/
theorem normalized_zeroLF_cover (B : Nat) (hb : 19007 ≤ B) :
    Cover (WeightedBound B) e0ZeroLF := by
  rw [zeroLF_is_exact_normalized_E0]
  exact monotone_cover hb BB6.Agent14E0LFParent.weighted

/-- Once ZeroLF is source accepted, the already-certified eleven E0 families
    plus exactly 55 complementary normalized rows suffice for the original
    Raw139 p0 Cover.  The eleven-family Covers, 43 sibling Covers, two
    continuation bridges, and terminal p7 Cover remain explicit premises. -/
theorem raw139_p0_from_55_with_zeroLF_source (B : Nat)
    (hb : 19007 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hEleven : ∀ q ∈ acceptedElevenCertified,
      Cover (WeightedBound B) q)
    (h55 : ∀ p ∈ normalizedAfterTwelveProspective,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 := by
  have hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q := by
    intro q hq
    simp only [acceptedTwelveProspective, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact normalized_zeroLF_cover B hb
    · exact hEleven q hq
  exact raw139_p0_cover_from_55_prospective B
    (Nat.le_trans (by decide : 59 ≤ 19007) hb)
    ha hTwelve h55 hrc hre hf

#print axioms zeroLF_is_exact_normalized_E0
#print axioms monotone_cover
#print axioms normalized_zeroLF_cover
#print axioms raw139_p0_from_55_with_zeroLF_source

end BB6.Agent14Raw139E0ZeroLF55AfterSource
