import Raw139NormalizedCertified19Finite
import Raw139NormalizedCertified18Native

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedCertified19Native

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve52
open BB6.Agent14Raw139NormalizedPostTwelve51
open BB6.Agent14Raw139NormalizedPostTwelve50
open BB6.Agent14Raw139NormalizedPostTwelve49
open BB6.Agent14Raw139NormalizedCertified18Finite
open BB6.Agent14Raw139NormalizedCertified18Native
open BB6.Agent14Raw139NormalizedCertified19Finite

theorem native_nineteen_to_B (B : Nat) (hb : 187672026 ≤ B)
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
    (hC1ZeroRA : Cover (WeightedBound 14876970) c1ZeroRA) :
    ∀ q ∈ sourceAcceptedNineteen, Cover (WeightedBound B) q := by
  intro q hq
  simp only [sourceAcceptedNineteen, List.mem_cons] at hq
  rcases hq with rfl | h18
  · exact mono_cover
      (Nat.le_trans (by decide : 14876970 ≤ 187672026) hb) hC1ZeroRA
  · exact native_eighteen_to_B B hb hSix hRF hRA hLB hLD hZeroRC
      hOneLC hF1ZeroLD hOneLF hC1ZeroLA hC1ZeroLC hOneLA hE0ZeroLC q h18

theorem raw139_p0_from_48_native (B : Nat) (hb : 187672026 ≤ B)
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
    (hC1ZeroRA : Cover (WeightedBound 14876970) c1ZeroRA)
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound B) (child r.1 r.2))
    (h48 : ∀ p ∈ normalizedAfterSourceAcceptedNineteen,
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
    (remainingTables_cover_from_48_certified B
      (native_nineteen_to_B B hb hSix hRF hRA hLB hLD hZeroRC
        hOneLC hF1ZeroLD hOneLF hC1ZeroLA hC1ZeroLC hOneLA hE0ZeroLC
        hC1ZeroRA)
      h48)
    hrc hre hf

#print axioms native_nineteen_to_B
#print axioms raw139_p0_from_48_native

end BB6.Agent14Raw139NormalizedCertified19Native
