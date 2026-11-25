import CanonicalTwoParentRosterOnly
import Raw117CanonicalCut
import Raw115Data
import Raw119Data
import Raw113Exact
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Canonical72RosterOnly

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement

/-- Six exact E1 sibling cylinders removed from the canonical 78-roster:
    raw107, raw113, raw114, raw115, raw117 and raw119. This module is
    deliberately independent of the champion-specific score wrapper. -/
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

/-- The source-rooted two-parent roster and raw117/raw119/raw115/raw113 cuts
    preserve the early 7014 dichotomy. The parent bounds are lifted to 7014;
    no champion-specific theorem is imported here. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  have hroot117 :=
    BB6.Agent8Raw117CanonicalCut.cut_sound (by decide)
      BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound
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

/-- Generic exactness at any target B≥7014. All 72 residual Covers and an
    attaining blank-start witness remain explicit premises. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent8Canonical72RosterOnly
