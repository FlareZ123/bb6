import CanonicalTwoParentAccepted
import Raw117CanonicalCut
import Raw115Data
import Raw119Data
import Raw113Exact
import Canonical77ExactComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Canonical72Raw107Raw113Raw114Raw115Raw117Raw119

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement

/-- Six exact E1 sibling cylinders removed from the canonical 78-roster:
    raw107, raw113, raw114, raw115, raw117 and raw119. -/
noncomputable def roster :=
  graftRoster BB6.Agent25Raw113.p113 []
    (graftRoster BB6.Agent8Raw115.p115 []
      (graftRoster BB6.Agent8Raw119.p119 []
        (BB6.Agent8Raw117CanonicalCut.cut
          BB6.Agent47CanonicalTwoParent.roster76)))

/-- The six parent cylinders are distinct canonical entries, leaving 72
    quotient representatives from the original 78. -/
theorem count : roster.length = 72 := by
  decide

/-- The source-accepted raw107/raw114 two-parent dichotomy, followed by
    raw117, raw119, raw115 and raw113, preserves the 7014 root bound. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  have hroot117 :=
    BB6.Agent8Raw117CanonicalCut.cut_sound (by decide)
      BB6.Agent11Raw107TwoParent.roster76_sound
  have h119 :
      ∀ m, compatible BB6.Agent8Raw119.p119 m →
        WeightedBound 7014 m := by
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent8Raw119.all119 m hm k d hk hd) (by decide)
  have h115 :
      ∀ m, compatible BB6.Agent8Raw115.p115 m →
        WeightedBound 7014 m := by
    intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent8Raw115.all115 m hm k d hk hd) (by decide)
  have hroot119 :=
    graftRoster_sound BB6.Agent8Raw119.p119_root
      hroot117
      (fun m hm => Or.inl (h119 m hm))
  have hroot115 :=
    graftRoster_sound BB6.Agent8Raw115.p115_root
      hroot119
      (fun m hm => Or.inl (h115 m hm))
  exact BB6.Agent25Raw113.graft113_sound (by decide) hroot115

/-- Exactness at any target B≥7014 now requires Covers for only 72
    retained quotient representatives. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

/-- Conditional exact BB(6) consumer at the published champion score. -/
theorem exact_from_canonical72_at_champion_score
    (hLeaves : ∀ e ∈ roster,
      Cover (WeightedBound BB6.Agent31Canonical77Exact.championScore) e.2) :
    BB6.Coverage.ExactBB6 BB6.Agent31Canonical77Exact.championScore :=
  exact_at_target BB6.Agent31Canonical77Exact.championScore
    (Nat.le_of_lt BB6.Agent31Canonical77Exact.champion_score_gt_7014)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms count
#print axioms sound
#print axioms exact_at_target
#print axioms exact_from_canonical72_at_champion_score

end BB6.Agent8Canonical72Raw107Raw113Raw114Raw115Raw117Raw119
