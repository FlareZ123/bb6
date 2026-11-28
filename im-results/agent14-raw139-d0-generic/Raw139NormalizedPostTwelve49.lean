import Raw139NormalizedPostTwelve50

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve49

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve50

/-- E0=1LA is independently source-certified at weighted bound 881,057
    (run 45936484460, theorem
    BB6.Agent48Raw139E0OneLA.all_completions_weighted). -/
def e0OneLA : PartialMachine := leaf (2, ⟨true, false, 0⟩)

theorem e0OneLA_occurs_once_after_twelve_plus_five :
    (normalizedAfterTwelvePlusFive.filter
      (fun p => sameTable p e0OneLA)).length = 1 := by
  decide

def normalizedAfterTwelvePlusSix : List PartialMachine :=
  normalizedAfterTwelvePlusFive.filter
    (fun p => !(sameTable p e0OneLA))

theorem normalizedAfterTwelvePlusSix_count :
    normalizedAfterTwelvePlusSix.length = 49 := by
  decide

theorem normalized50_cover_from_49 (B : Nat)
    (hOneLA : Cover (WeightedBound B) e0OneLA)
    (h49 : ∀ p ∈ normalizedAfterTwelvePlusSix,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedAfterTwelvePlusFive,
      Cover (WeightedBound B) p := by
  intro p hp
  by_cases h : sameTable p e0OneLA = true
  · rw [sameTable_sound h]
    exact hOneLA
  · exact h49 p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

theorem raw139_p0_cover_from_49 (B : Nat)
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
    (hOneLA : Cover (WeightedBound B) e0OneLA)
    (h49 : ∀ p ∈ normalizedAfterTwelvePlusSix,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_50 B hb ha hTwelve hExtraTwo hOneLF hZeroLA hZeroLC
    (normalized50_cover_from_49 B hOneLA h49) hrc hre hf

#print axioms e0OneLA_occurs_once_after_twelve_plus_five
#print axioms normalizedAfterTwelvePlusSix_count
#print axioms normalized50_cover_from_49
#print axioms raw139_p0_cover_from_49

end BB6.Agent14Raw139NormalizedPostTwelve49
