import CanonicalRaw114Accepted
import TM63RawUpperInterface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical77Exact

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6ChampionArithmetic
open BB6Coverage.Agent48DirectRoot

/-- The attained primitive-step score of the published blank-start champion. -/
abbrev championScore : Nat := proposedTM63Moves + 7

/-- The exact champion score strictly exceeds the raw114 parent bound. -/
theorem champion_score_gt_7014 : 7014 < championScore := by
  have hroot : 27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 :=
    rootSteps_le_score 27959 3 7 6 63
  change 7014 < proposedTM63Moves + 7
  rw [← threeSectionMoves_root]
  omega

/-- The current 77-residual canonical quotient roster, covered at the attained
score, proves the exact global BB(6) value.  The only premise is a Cover for
each retained residual; champion membership in any particular residual is
not required by this consumer. -/
theorem exact_from_canonical77_at_champion_score
    (hLeaves : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent47CanonicalRaw114Accepted.exact_at_target championScore
    (Nat.le_of_lt champion_score_gt_7014) hLeaves champion_raw_witness

#print axioms champion_score_gt_7014
#print axioms champion_raw_witness
#print axioms BB6.Agent47CanonicalRaw114Accepted.exact_at_target
#print axioms exact_from_canonical77_at_champion_score

end BB6.Agent31Canonical77Exact
