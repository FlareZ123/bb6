import CanonicalRaw114Accepted
import Raw121Data
import CanonicalRosterRefinement
import Canonical77ExactComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw121Canonical77Graft

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement
open BB6Coverage.Agent48DirectRoot

/-- Graft the source-audited Raw121 parent into the accepted 77-entry
    quotient roster obtained after the Raw114 cut. -/
noncomputable def roster76 :=
  graftRoster BB6.Agent11Raw121.p121 []
    BB6.Agent47CanonicalRaw114Accepted.roster

/-- Raw121 is a distinct retained representative of the accepted canonical77
    roster, so its complete parent bound removes exactly one entry. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      sameTable e.2 BB6.Agent11Raw121.p121 = true := by
  decide

theorem roster76_count : roster76.length = 76 := by
  decide

/-- Mixed-bound quotient dichotomy: the accepted canonical77 interface gives
    7014, and Raw121's original-source 4063 bound is lifted to that cutoff. -/
theorem roster76_sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster76, TNFQuotientCompatible e.2 m :=
  graftRoster_sound BB6.Agent11Raw121.p121_root
    BB6.Agent47CanonicalRaw114Accepted.sound
    (fun m hm => Or.inl (by
      intro k d hk hd
      exact Nat.le_trans
        (BB6.Agent11Raw121.all121 m hm k d hk hd)
        (by decide)))

/-- Conditional exactness after the Raw121 graft. Only the 76 retained
    quotient representatives still require Covers at the attained score. -/
theorem exact_from_canonical76_at_champion_score
    (hLeaves : ∀ e ∈ roster76,
      Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6
      BB6.Agent31Canonical77Exact.championScore :=
  exact_from_quotient_roster
    (by omega)
    (Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014)
    roster76_sound
    hLeaves
    champion_raw_witness

#print axioms parent_present
#print axioms roster76_count
#print axioms roster76_sound
#print axioms exact_from_canonical76_at_champion_score

end BB6.Agent11Raw121Canonical77Graft
