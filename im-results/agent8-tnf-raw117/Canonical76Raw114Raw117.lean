import CanonicalRaw114Accepted
import Raw117CanonicalCut
import Canonical77ExactComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Canonical76Raw114Raw117

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot

/-- Apply the independently source-accepted raw117 exact-table cut to the
    source-accepted 77-residual raw114 roster. -/
noncomputable def roster :=
  BB6.Agent8Raw117CanonicalCut.cut BB6.Agent47CanonicalRaw114Accepted.roster

/-- The raw117 E1=1RD sibling is distinct from the already-ingested raw114
    E1=0LD sibling, so one further canonical residual is removed. -/
theorem count : roster.length = 76 := by
  decide

/-- Mixed proof composition: the old raw114 roster has a 7014 dichotomy;
    raw117's 1291 cylinder bound removes its one matching entry. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  BB6.Agent8Raw117CanonicalCut.cut_sound (by decide)
    BB6.Agent47CanonicalRaw114Accepted.sound

/-- Exactness at any target B≥7014 now requires Covers for only 76 retained
    quotient representatives. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

/-- The concrete published champion score is the target for the remaining
    76 Covers; champion membership in a particular residual is unnecessary. -/
theorem exact_from_canonical76_at_champion_score
    (hLeaves : ∀ e ∈ roster,
      Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent31Canonical77Exact.championScore :=
  exact_at_target BB6.Agent31Canonical77Exact.championScore
    (Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms count
#print axioms sound
#print axioms exact_at_target
#print axioms exact_from_canonical76_at_champion_score

end BB6.Agent8Canonical76Raw114Raw117
