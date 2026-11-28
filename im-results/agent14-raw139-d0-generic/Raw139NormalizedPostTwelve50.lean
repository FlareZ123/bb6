import Raw139NormalizedPostTwelve51

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve50

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve52
open BB6.Agent14Raw139NormalizedPostTwelve51

/-- C1=0LC is independently source-certified at weighted bound 321
    (run 45596109440, theorem BB6.Agent6C1ZeroLC.cover_zeroLC). -/
def c1ZeroLC : PartialMachine := leaf (4, ⟨false, false, 2⟩)

theorem c1ZeroLC_occurs_once_after_twelve_plus_four :
    (normalizedAfterTwelvePlusFour.filter
      (fun p => sameTable p c1ZeroLC)).length = 1 := by
  decide

def normalizedAfterTwelvePlusFive : List PartialMachine :=
  normalizedAfterTwelvePlusFour.filter
    (fun p => !(sameTable p c1ZeroLC))

theorem normalizedAfterTwelvePlusFive_count :
    normalizedAfterTwelvePlusFive.length = 50 := by
  decide

theorem normalized51_cover_from_50 (B : Nat)
    (hZeroLC : Cover (WeightedBound B) c1ZeroLC)
    (h50 : ∀ p ∈ normalizedAfterTwelvePlusFive,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedAfterTwelvePlusFour,
      Cover (WeightedBound B) p := by
  intro p hp
  by_cases h : sameTable p c1ZeroLC = true
  · rw [sameTable_sound h]
    exact hZeroLC
  · exact h50 p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

/-- Exact Raw139 p0 interface after the source-accepted C1=0LC cylinder is
    additionally exposed: only 50 complementary normalized table Covers
    remain beyond the previously removed twelve E0, C1=1LC, F1=0LD,
    E0=1LF, and C1=0LA cylinders. -/
theorem raw139_p0_cover_from_50 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (hExtraTwo : ∀ q ∈ sourceAcceptedExtraTwo,
      Cover (WeightedBound B) q)
    (hOneLF : Cover (WeightedBound B) e0OneLF)
    (hZeroLA : Cover (WeightedBound B) c1ZeroLA)
    (hZeroLC : Cover (WeightedBound B) c1ZeroLC)
    (h50 : ∀ p ∈ normalizedAfterTwelvePlusFive,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_51 B hb ha hTwelve hExtraTwo hOneLF hZeroLA
    (normalized51_cover_from_50 B hZeroLC h50) hrc hre hf

#print axioms c1ZeroLC_occurs_once_after_twelve_plus_four
#print axioms normalizedAfterTwelvePlusFive_count
#print axioms normalized51_cover_from_50
#print axioms raw139_p0_cover_from_50

end BB6.Agent14Raw139NormalizedPostTwelve50
