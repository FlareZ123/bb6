import Raw139NormalizedCertified18Native
import Raw139NormalizedLocalAcceptedCovers

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedCertified18ChampionNative

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
open BB6.Agent14Raw139NormalizedPostTwelve48
open BB6.Agent14Raw139NormalizedCertified18Finite
open BB6.Agent14Raw139NormalizedCertified18Native
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent38ChampionThreshold

/-- The largest native cutoff among the eighteen independently accepted parent
    cylinders is still far below the attained champion score.  This symbolic
    route deliberately avoids evaluating the enormous closed score. -/
theorem localScore_ge_accepted18_native :
    187672026 ≤ localScore :=
  Nat.le_trans
    (by decide : 187672026 ≤ 2^63)
    champion_score_ge_pow63

/-- Roster-independent champion-score Raw139 interface after all eighteen
    independently accepted normalized parent cylinders are transported from
    their genuine native bounds.  The 43 sibling cylinders, both exceptional
    continuation lifts, and terminal p7 are consumed by the existing local
    accepted-spine theorem.  Exactly the 49 normalized residual rows remain. -/
theorem raw139_p0_at_champion_from_49_native
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
    (h49 : ∀ p ∈ normalizedAfterSourceAcceptedEighteen,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover_after_accepted_local
    (remainingTables_cover_from_49_certified localScore
      (native_eighteen_to_B localScore localScore_ge_accepted18_native
        hSix hRF hRA hLB hLD hZeroRC hOneLC hF1ZeroLD
        hOneLF hC1ZeroLA hC1ZeroLC hOneLA hE0ZeroLC)
      h49)

#print axioms localScore_ge_accepted18_native
#print axioms raw139_p0_at_champion_from_49_native

end BB6.Agent14Raw139NormalizedCertified18ChampionNative
