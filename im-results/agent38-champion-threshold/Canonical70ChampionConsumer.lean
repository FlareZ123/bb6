import Canonical70Raw121Raw110RosterOnly
import ChampionScoreLowerBound

namespace BB6.Agent38ChampionThreshold

open BB6ChampionArithmetic
open BB6Coverage

/-- The exact champion witness and the champion-independent 70-roster
    dichotomy combine into an exact-BB(6) theorem, conditional only on the
    70 retained quotient Covers at the attained score. -/
theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent8Canonical70Raw121Raw110RosterOnly.roster,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent8Canonical70Raw121Raw110RosterOnly.exact_at_target
    (proposedTM63Moves + 7)
    champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms exact_at_champion_score

end BB6.Agent38ChampionThreshold
