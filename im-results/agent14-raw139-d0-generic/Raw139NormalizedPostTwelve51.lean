import Raw139NormalizedPostTwelve52

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve51

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve52

/-- C1=0LA is independently source-certified at weighted bound 266
    (run 45596109440, theorem BB6.Agent6C1ZeroLAParent.cover_zeroLA). -/
def c1ZeroLA : PartialMachine := leaf (4, ⟨false, false, 0⟩)

theorem c1ZeroLA_occurs_once_after_twelve_plus_three :
    (normalizedAfterTwelvePlusThree.filter
      (fun p => sameTable p c1ZeroLA)).length = 1 := by
  decide

def normalizedAfterTwelvePlusFour : List PartialMachine :=
  normalizedAfterTwelvePlusThree.filter
    (fun p => !(sameTable p c1ZeroLA))

theorem normalizedAfterTwelvePlusFour_count :
    normalizedAfterTwelvePlusFour.length = 51 := by
  decide

theorem normalized52_cover_from_51 (B : Nat)
    (hZeroLA : Cover (WeightedBound B) c1ZeroLA)
    (h51 : ∀ p ∈ normalizedAfterTwelvePlusFour,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedAfterTwelvePlusThree,
      Cover (WeightedBound B) p := by
  intro p hp
  by_cases h : sameTable p c1ZeroLA = true
  · rw [sameTable_sound h]
    exact hZeroLA
  · exact h51 p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

/-- Exact Raw139 p0 interface after the source-accepted C1=0LA cylinder is
    additionally exposed: only 51 complementary normalized table Covers
    remain beyond the previously removed twelve E0, C1=1LC, F1=0LD,
    and E0=1LF cylinders. -/
theorem raw139_p0_cover_from_51 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (hExtraTwo : ∀ q ∈ sourceAcceptedExtraTwo,
      Cover (WeightedBound B) q)
    (hOneLF : Cover (WeightedBound B) e0OneLF)
    (hZeroLA : Cover (WeightedBound B) c1ZeroLA)
    (h51 : ∀ p ∈ normalizedAfterTwelvePlusFour,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_52 B hb ha hTwelve hExtraTwo hOneLF
    (normalized52_cover_from_51 B hZeroLA h51) hrc hre hf

#print axioms c1ZeroLA_occurs_once_after_twelve_plus_three
#print axioms normalizedAfterTwelvePlusFour_count
#print axioms normalized52_cover_from_51
#print axioms raw139_p0_cover_from_51

end BB6.Agent14Raw139NormalizedPostTwelve51
