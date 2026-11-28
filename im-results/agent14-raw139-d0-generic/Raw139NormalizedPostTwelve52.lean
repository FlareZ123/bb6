import Raw139NormalizedPostTwelve53

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve52

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53

/-- E0=1LF is now independently source-certified at weighted bound 90,794
    (run 46093526398, theorem BB6.Agent6E0OneLF.weighted). -/
def e0OneLF : PartialMachine := leaf (2, ⟨true, false, 5⟩)

theorem e0OneLF_occurs_once_after_twelve_plus_two :
    (normalizedAfterTwelvePlusTwo.filter
      (fun p => sameTable p e0OneLF)).length = 1 := by
  decide

def normalizedAfterTwelvePlusThree : List PartialMachine :=
  normalizedAfterTwelvePlusTwo.filter
    (fun p => !(sameTable p e0OneLF))

theorem normalizedAfterTwelvePlusThree_count :
    normalizedAfterTwelvePlusThree.length = 52 := by
  decide

/-- Reinsert the newly source-certified E0=1LF cylinder into the exact
    52-table complement. -/
theorem normalized53_cover_from_52 (B : Nat)
    (hOneLF : Cover (WeightedBound B) e0OneLF)
    (h52 : ∀ p ∈ normalizedAfterTwelvePlusThree,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedAfterTwelvePlusTwo,
      Cover (WeightedBound B) p := by
  intro p hp
  by_cases h : sameTable p e0OneLF = true
  · rw [sameTable_sound h]
    exact hOneLF
  · exact h52 p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

/-- Exact original Raw139 p0 frontier after twelve E0 cylinders, the two
    previously source-accepted C1/F1 cylinders, and the newly accepted
    E0=1LF cylinder are exposed as parent premises: only 52 complementary
    normalized table Covers remain. -/
theorem raw139_p0_cover_from_52 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (hExtraTwo : ∀ q ∈ sourceAcceptedExtraTwo,
      Cover (WeightedBound B) q)
    (hOneLF : Cover (WeightedBound B) e0OneLF)
    (h52 : ∀ p ∈ normalizedAfterTwelvePlusThree,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_53 B hb ha hTwelve hExtraTwo
    (normalized53_cover_from_52 B hOneLF h52) hrc hre hf

#print axioms e0OneLF_occurs_once_after_twelve_plus_two
#print axioms normalizedAfterTwelvePlusThree_count
#print axioms normalized53_cover_from_52
#print axioms raw139_p0_cover_from_52

end BB6.Agent14Raw139NormalizedPostTwelve52
