import CanonicalRaw114Accepted
import Raw117CanonicalCut
import Canonical77ExactComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Canonical75Raw107Raw114Raw117

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot

/-- If the raw107 parent bound is established, the existing p107+p114
    76-roster admits the independent raw117 exact-table cut as well. -/
noncomputable def roster :=
  BB6.Agent8Raw117CanonicalCut.cut BB6.Agent47CanonicalTwoParent.roster76

/-- The three distinct E1 siblings p107, p114 and p117 remove three entries
    from the 78-entry canonical roster. -/
theorem count : roster.length = 75 := by
  decide

/-- Conditional 75-residual quotient dichotomy; only the p107 parent bound
    remains as an external mathematical premise. -/
theorem sound
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m) :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  BB6.Agent8Raw117CanonicalCut.cut_sound (by decide)
    (BB6.Agent47CanonicalRaw114Accepted.two_parent_sound h107)

/-- Exactness at any target B≥7014, conditional only on p107 and Covers for
    the 75 retained quotient representatives. -/
theorem exact_at_target (h107 :
    ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound h107) hLeaves champ

/-- Conditional exact BB(6) consumer at the published champion score. -/
theorem exact_from_canonical75_at_champion_score (h107 :
    ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (hLeaves : ∀ e ∈ roster,
      Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent31Canonical77Exact.championScore :=
  exact_at_target h107 BB6.Agent31Canonical77Exact.championScore
    (Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms count
#print axioms sound
#print axioms exact_at_target
#print axioms exact_from_canonical75_at_champion_score

end BB6.Agent8Canonical75Raw107Raw114Raw117
