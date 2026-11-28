import Raw139NormalizedCertified18Finite
import Raw139NormalizedE0TenNativeBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedCertified18Native

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedE0TenNativeBounds
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve52
open BB6.Agent14Raw139NormalizedPostTwelve51
open BB6.Agent14Raw139NormalizedPostTwelve50
open BB6.Agent14Raw139NormalizedPostTwelve49
open BB6.Agent14Raw139NormalizedPostTwelve48
open BB6.Agent14Raw139NormalizedCertified18Finite

theorem native_eleven_to_B (B : Nat) (hb : 187672026 ≤ B)
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (hZeroRC : Cover (WeightedBound 1673363) e0ZeroRC) :
    ∀ q ∈ acceptedElevenCertified, Cover (WeightedBound B) q := by
  intro q hq
  simp only [acceptedElevenCertified, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact mono_cover
      (Nat.le_trans (by decide : 1673363 ≤ 187672026) hb) hZeroRC
  · exact native_ten_to_B B hb hSix hRF hRA hLB hLD q hq

theorem native_extra_two_to_B (B : Nat) (hb : 187672026 ≤ B)
    (hOneLC : Cover (WeightedBound 598)
      (leaf (4, ⟨true, false, 2⟩)))
    (hF1ZeroLD : Cover (WeightedBound 124)
      (leaf (5, ⟨false, false, 3⟩))) :
    ∀ q ∈ sourceAcceptedExtraTwo, Cover (WeightedBound B) q := by
  intro q hq
  simp only [sourceAcceptedExtraTwo, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl | rfl
  · exact mono_cover
      (Nat.le_trans (by decide : 598 ≤ 187672026) hb) hOneLC
  · exact mono_cover
      (Nat.le_trans (by decide : 124 ≤ 187672026) hb) hF1ZeroLD

def sourceAcceptedPostTwelveFive : List PartialMachine :=
  [e0OneLF, c1ZeroLA, c1ZeroLC, e0OneLA, e0ZeroLC]

theorem native_post_twelve_five_to_B (B : Nat) (hb : 187672026 ≤ B)
    (hOneLF : Cover (WeightedBound 90794) e0OneLF)
    (hC1ZeroLA : Cover (WeightedBound 266) c1ZeroLA)
    (hC1ZeroLC : Cover (WeightedBound 321) c1ZeroLC)
    (hOneLA : Cover (WeightedBound 881057) e0OneLA)
    (hE0ZeroLC : Cover (WeightedBound 80377) e0ZeroLC) :
    ∀ q ∈ sourceAcceptedPostTwelveFive, Cover (WeightedBound B) q := by
  intro q hq
  simp only [sourceAcceptedPostTwelveFive, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact mono_cover
      (Nat.le_trans (by decide : 90794 ≤ 187672026) hb) hOneLF
  · exact mono_cover
      (Nat.le_trans (by decide : 266 ≤ 187672026) hb) hC1ZeroLA
  · exact mono_cover
      (Nat.le_trans (by decide : 321 ≤ 187672026) hb) hC1ZeroLC
  · exact mono_cover
      (Nat.le_trans (by decide : 881057 ≤ 187672026) hb) hOneLA
  · exact mono_cover
      (Nat.le_trans (by decide : 80377 ≤ 187672026) hb) hE0ZeroLC

theorem sourceAcceptedEighteen_decompose :
    sourceAcceptedEighteen =
      acceptedElevenCertified ++ sourceAcceptedExtraTwo ++
        sourceAcceptedPostTwelveFive := by
  rfl

/-- All eighteen accepted Raw139 parent cylinders transported to one common
    bound using their actual independently accepted native cutoffs. -/
theorem native_eighteen_to_B (B : Nat) (hb : 187672026 ≤ B)
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (hZeroRC : Cover (WeightedBound 1673363) e0ZeroRC)
    (hOneLC : Cover (WeightedBound 598)
      (leaf (4, ⟨true, false, 2⟩)))
    (hF1ZeroLD : Cover (WeightedBound 124)
      (leaf (5, ⟨false, false, 3⟩)))
    (hOneLF : Cover (WeightedBound 90794) e0OneLF)
    (hC1ZeroLA : Cover (WeightedBound 266) c1ZeroLA)
    (hC1ZeroLC : Cover (WeightedBound 321) c1ZeroLC)
    (hOneLA : Cover (WeightedBound 881057) e0OneLA)
    (hE0ZeroLC : Cover (WeightedBound 80377) e0ZeroLC) :
    ∀ q ∈ sourceAcceptedEighteen, Cover (WeightedBound B) q := by
  rw [sourceAcceptedEighteen_decompose]
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with h11 | hrest
  · exact native_eleven_to_B B hb hSix hRF hRA hLB hLD hZeroRC q h11
  · rcases hrest with h2 | h5
    · exact native_extra_two_to_B B hb hOneLC hF1ZeroLD q h2
    · exact native_post_twelve_five_to_B B hb
        hOneLF hC1ZeroLA hC1ZeroLC hOneLA hE0ZeroLC q h5

/-- Exact Raw139 p0 reduction with all eighteen accepted parent cylinders
    wired at their native bounds.  Only 49 normalized residual Covers and the
    unchanged original Raw139 spine premises remain. -/
theorem raw139_p0_from_49_native (B : Nat) (hb : 187672026 ≤ B)
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (hZeroRC : Cover (WeightedBound 1673363) e0ZeroRC)
    (hOneLC : Cover (WeightedBound 598)
      (leaf (4, ⟨true, false, 2⟩)))
    (hF1ZeroLD : Cover (WeightedBound 124)
      (leaf (5, ⟨false, false, 3⟩)))
    (hOneLF : Cover (WeightedBound 90794) e0OneLF)
    (hC1ZeroLA : Cover (WeightedBound 266) c1ZeroLA)
    (hC1ZeroLC : Cover (WeightedBound 321) c1ZeroLC)
    (hOneLA : Cover (WeightedBound 881057) e0OneLA)
    (hE0ZeroLC : Cover (WeightedBound 80377) e0ZeroLC)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (h49 : ∀ p ∈ normalizedAfterSourceAcceptedEighteen,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_cover B
    (Nat.le_trans (by decide : 59 ≤ 187672026) hb)
    ha
    (remainingTables_cover_from_49_certified B
      (native_eighteen_to_B B hb hSix hRF hRA hLB hLD hZeroRC
        hOneLC hF1ZeroLD hOneLF hC1ZeroLA hC1ZeroLC hOneLA hE0ZeroLC)
      h49)
    hrc hre hf

#print axioms native_eleven_to_B
#print axioms native_extra_two_to_B
#print axioms native_post_twelve_five_to_B
#print axioms sourceAcceptedEighteen_decompose
#print axioms native_eighteen_to_B
#print axioms raw139_p0_from_49_native

end BB6.Agent14Raw139NormalizedCertified18Native
