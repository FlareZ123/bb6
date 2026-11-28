import Raw139NormalizedE0ElevenCertifiedConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve53

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedConditional

/-- Two exact normalized rows whose whole cylinders already have independent
    original-source weighted Covers:
    * C1=1LC, source run 45581126485, bound 598;
    * F1=0LD, source run 45612965271, bound 124. -/
def sourceAcceptedExtraTwo : List PartialMachine := [
  leaf (4, ⟨true, false, 2⟩),
  leaf (5, ⟨false, false, 3⟩)
]

theorem sourceAcceptedExtraTwo_each_once :
    ∀ q ∈ sourceAcceptedExtraTwo,
      (normalizedAfterTwelveProspective.filter
        (fun p => sameTable p q)).length = 1 := by
  decide

theorem sourceAcceptedExtraTwo_distinct :
    sameTable
      (leaf (4, ⟨true, false, 2⟩))
      (leaf (5, ⟨false, false, 3⟩)) = false := by
  decide

def normalizedAfterTwelvePlusTwo : List PartialMachine :=
  normalizedAfterTwelveProspective.filter
    (fun p => !(matchesAny p sourceAcceptedExtraTwo))

theorem normalizedAfterTwelvePlusTwo_count :
    normalizedAfterTwelvePlusTwo.length = 53 := by
  decide

/-- Reinsert the two independently closed cylinders into the exact
    53-table complement. -/
theorem normalized55_cover_from_53 (B : Nat)
    (hExtra : ∀ q ∈ sourceAcceptedExtraTwo,
      Cover (WeightedBound B) q)
    (h53 : ∀ p ∈ normalizedAfterTwelvePlusTwo,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedAfterTwelveProspective,
      Cover (WeightedBound B) p := by
  intro p hp
  by_cases h : matchesAny p sourceAcceptedExtraTwo = true
  · obtain ⟨q, hq, hsame⟩ := matchesAny_witness h
    rw [sameTable_sound hsame]
    exact hExtra q hq
  · exact h53 p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

/-- Exact original Raw139 p0 frontier after twelve E0 cylinders and the two
    already source-accepted C1/F1 cylinders are exposed as parent premises:
    only 53 complementary normalized table Covers remain. -/
theorem raw139_p0_cover_from_53 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (hExtra : ∀ q ∈ sourceAcceptedExtraTwo,
      Cover (WeightedBound B) q)
    (h53 : ∀ p ∈ normalizedAfterTwelvePlusTwo,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_55_prospective B hb ha hTwelve
    (normalized55_cover_from_53 B hExtra h53) hrc hre hf

#print axioms sourceAcceptedExtraTwo_each_once
#print axioms sourceAcceptedExtraTwo_distinct
#print axioms normalizedAfterTwelvePlusTwo_count
#print axioms normalized55_cover_from_53
#print axioms raw139_p0_cover_from_53

end BB6.Agent14Raw139NormalizedPostTwelve53
