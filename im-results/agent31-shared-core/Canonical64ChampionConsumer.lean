import Canonical64Raw120Integrated
import ChampionScoreLowerBound

namespace BB6.Agent31Canonical64Champion

open BB6Coverage
open BB6ChampionArithmetic

/-- The accepted Canonical64 roster theorem, the exact named champion
    witness, and the proved score-floor inequality combine into a
    champion-specific exactness interface. Only the 64 retained Covers
    remain as hypotheses. -/
theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent3Canonical64Raw120.roster64,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent3Canonical64Raw120.exact_at_target
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms BB6Coverage.Agent48DirectRoot.champion_raw_witness
#print axioms BB6.Agent38ChampionThreshold.champion_score_ge_6766859
#print axioms exact_at_champion_score

end BB6.Agent31Canonical64Champion
