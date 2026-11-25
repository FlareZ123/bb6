import CanonicalTwoParentAccepted
import Raw121Data
import CanonicalFrontier
import CanonicalRosterRefinement
import Canonical77ExactComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw121CanonicalGraft

open BB6Coverage BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent50TNFPilot

/-- Remove the independently certified Raw121 parent from the 76-entry
    roster already obtained by the Raw107/Raw114 grafts. -/
noncomputable def roster75 :=
  graftRoster BB6.Agent11Raw121.p121 [] BB6.Agent47CanonicalTwoParent.roster76

/-- The Raw121 parent is a distinct member of the two-parent residual roster;
    the exact finite computation leaves 75 representatives. -/
theorem roster75_count : roster75.length = 75 := by decide

/-- The three source-certified parents give a mixed-threshold dichotomy:
    Raw107 is bounded by 815, Raw114 by 7014, and Raw121 by 4063 (lifted
    monotonically to 7014). Every other case remains in the 75-entry roster. -/
theorem roster75_sound
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (h114 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p114 m →
      WeightedBound 7014 m) :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster75, TNFQuotientCompatible e.2 m :=
  graftRoster_sound BB6.Agent11Raw121.p121_root
    (BB6.Agent11Raw107TwoParent.roster76_sound h107 h114)
    (fun m hm => Or.inl (by
      intro k d hk hd
      exact Nat.le_trans
        (BB6.Agent11Raw121.all121 m hm k d hk hd)
        (by decide))

/-- Conditional exactness after all three parent cuts. The remaining 75
    quotient-compatible residuals still require Covers at the attained B. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (h114 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p114 m →
      WeightedBound 7014 m)
    (hLeaves : ∀ e ∈ roster75, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (roster75_sound h107 h114)
    hLeaves champ

/-- Concrete conditional consumer using the already source-certified Raw107,
    Raw114, and Raw121 parent bounds. -/
theorem exact_from_canonical75_at_champion_score
    (hLeaves : ∀ e ∈ roster75,
      Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent31Canonical77Exact.championScore :=
  exact_at_target
    BB6.Agent31Canonical77Exact.championScore
    (Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014)
    BB6.Agent11Raw107TwoParent.p107_bound
    BB6.Agent11Raw107TwoParent.p114_bound
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms roster75_count
#print axioms roster75_sound
#print axioms exact_at_target
#print axioms exact_from_canonical75_at_champion_score

end BB6.Agent11Raw121CanonicalGraft
