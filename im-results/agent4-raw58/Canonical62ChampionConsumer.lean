import Canonical62Raw112Raw58Integrated
import Canonical64ChampionConsumer

namespace BB6.Agent4Canonical62Champion

open BB6Coverage
open BB6ChampionArithmetic

/-- Reuse the accepted Canonical64 score/witness boundary, while the
    two-parent Canonical62 quotient interface leaves only 62 score-Covers. -/
theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent4Canonical62Raw112Raw58.roster62,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent4Canonical62Raw112Raw58.exact_at_target62
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms exact_at_champion_score

end BB6.Agent4Canonical62Champion
