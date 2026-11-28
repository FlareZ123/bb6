import Raw139NormalizedPostTwelve49

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedPostTwelve48

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve52
open BB6.Agent14Raw139NormalizedPostTwelve51
open BB6.Agent14Raw139NormalizedPostTwelve50
open BB6.Agent14Raw139NormalizedPostTwelve49

/-- E0=0LC is independently source-certified at weighted bound 80,377
    (run 45968078984, theorem BB6.Agent6E0ZeroLCExact.weighted). -/
def e0ZeroLC : PartialMachine := leaf (2, ⟨false, false, 2⟩)

theorem e0ZeroLC_occurs_once_after_twelve_plus_six :
    (normalizedAfterTwelvePlusSix.filter
      (fun p => sameTable p e0ZeroLC)).length = 1 := by
  decide

def normalizedAfterTwelvePlusSeven : List PartialMachine :=
  normalizedAfterTwelvePlusSix.filter
    (fun p => !(sameTable p e0ZeroLC))

theorem normalizedAfterTwelvePlusSeven_count :
    normalizedAfterTwelvePlusSeven.length = 48 := by
  decide

theorem normalized49_cover_from_48 (B : Nat)
    (hZeroLC : Cover (WeightedBound B) e0ZeroLC)
    (h48 : ∀ p ∈ normalizedAfterTwelvePlusSeven,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedAfterTwelvePlusSix,
      Cover (WeightedBound B) p := by
  intro p hp
  by_cases h : sameTable p e0ZeroLC = true
  · rw [sameTable_sound h]
    exact hZeroLC
  · exact h48 p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

theorem raw139_p0_cover_from_48 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (hExtraTwo : ∀ q ∈ sourceAcceptedExtraTwo,
      Cover (WeightedBound B) q)
    (hOneLF : Cover (WeightedBound B) e0OneLF)
    (hZeroLA : Cover (WeightedBound B) c1ZeroLA)
    (hC1ZeroLC : Cover (WeightedBound B) c1ZeroLC)
    (hOneLA : Cover (WeightedBound B) e0OneLA)
    (hE0ZeroLC : Cover (WeightedBound B) e0ZeroLC)
    (h48 : ∀ p ∈ normalizedAfterTwelvePlusSeven,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_49 B hb ha hTwelve hExtraTwo hOneLF hZeroLA hC1ZeroLC hOneLA
    (normalized49_cover_from_48 B hE0ZeroLC h48) hrc hre hf

#print axioms e0ZeroLC_occurs_once_after_twelve_plus_six
#print axioms normalizedAfterTwelvePlusSeven_count
#print axioms normalized49_cover_from_48
#print axioms raw139_p0_cover_from_48

end BB6.Agent14Raw139NormalizedPostTwelve48
