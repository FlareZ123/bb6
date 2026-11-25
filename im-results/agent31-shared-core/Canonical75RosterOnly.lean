import CanonicalTwoParentRosterOnly
import Raw117CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical75RosterOnly

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- Add the original-source-accepted raw117 cylinder to the raw107+raw114
    quotient roster, without importing the champion proof. -/
noncomputable def roster :=
  BB6.Agent8Raw117CanonicalCut.cut BB6.Agent47CanonicalTwoParent.roster76

/-- The exact raw117 table removes one more entry from the 76-roster. -/
theorem count : roster.length = 75 := by
  decide

/-- Mixed-bound composition retains the 7014 root branch and every
    uncovered quotient-compatible child. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  BB6.Agent8Raw117CanonicalCut.cut_sound (by decide)
    BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound

/-- Generic exactness at any B≥7014; all 75 residual Covers and an attaining
    blank-start witness remain explicit premises. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent31Canonical75RosterOnly
