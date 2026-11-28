import Raw139NormalizedE0TenAcceptedConditional
import E0ZeroLFDischarge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139E0ZeroLF56AfterSource

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedConditional

/-- The source-certified six-hole ZeroLF parent coincides with exactly the
    same physical normalized E0 row, not with an informal code abbreviation. -/
theorem zeroLF_is_exact_normalized_E0 :
    e0ZeroLF = BB6.Agent14E0LFParent.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

/-- Transport a verified finite weighted Cover to a larger time cutoff. -/
theorem monotone_cover {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (h.sound m hm k d hk hd) hAB

/-- First unconditional original-source ZeroLF normalized E0 Cover, at any
    B >= 19007, after the exact 3862 source proof is joined to the parent. -/
theorem normalized_zeroLF_cover (B : Nat) (hb : 19007 ≤ B) :
    Cover (WeightedBound B) e0ZeroLF := by
  rw [zeroLF_is_exact_normalized_E0]
  exact monotone_cover hb BB6.Agent14E0LFParent.weighted

/-- The eleventh parent Cover is no longer a premise: the only E0 Cover
    assumptions are the *other ten* independently accepted families, plus
    the 56 normalized residuals. All 43 accepted siblings, rowRC/rowRE
    continuations and terminal p7 Cover remain explicit assumptions. -/
theorem raw139_p0_from_56_with_zeroLF_source (B : Nat)
    (hb : 19007 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hTen : ∀ q ∈ acceptedE0Ten, Cover (WeightedBound B) q)
    (h56 : ∀ p ∈ normalizedAfterEleven, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 := by
  have hEleven : ∀ q ∈ acceptedE0Eleven,
      Cover (WeightedBound B) q := by
    intro q hq
    simp only [acceptedE0Eleven, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact normalized_zeroLF_cover B hb
    · exact hTen q hq
  exact raw139_p0_cover_from_56 B
    (Nat.le_trans (by decide : 59 ≤ 19007) hb)
    ha hEleven h56 hrc hre hf

#print axioms zeroLF_is_exact_normalized_E0
#print axioms monotone_cover
#print axioms normalized_zeroLF_cover
#print axioms raw139_p0_from_56_with_zeroLF_source

end BB6.Agent14Raw139E0ZeroLF56AfterSource
