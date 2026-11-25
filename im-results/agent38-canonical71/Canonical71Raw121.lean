import Canonical72RosterOnly
import Raw121Data
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Canonical71Raw121

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement

/-- Raw121 is a distinct retained representative of the six-cut
    canonical72 roster. -/
theorem raw121_parent_present :
    ∃ e ∈ BB6.Agent8Canonical72RosterOnly.roster,
      sameTable e.2 BB6.Agent11Raw121.p121 = true := by
  decide

/-- Add the source-accepted E1=1RE cylinder to the six-cut canonical72
    roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent11Raw121.p121 []
    BB6.Agent8Canonical72RosterOnly.roster

/-- The raw121 parent removes exactly one further canonical residual. -/
theorem count : roster.length = 71 := by
  decide

/-- Mixed-bound root dichotomy. The canonical72 route gives 7014;
    raw121's original-source parent certificate gives 4063 and is lifted
    monotonically to the common 7014 target. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound BB6.Agent11Raw121.p121_root
    BB6.Agent8Canonical72RosterOnly.sound
    (fun m hm => Or.inl (by
      intro k d hk hd
      exact Nat.le_trans
        (BB6.Agent11Raw121.all121 m hm k d hk hd)
        (by decide)))

/-- Conditional exactness at any target B≥7014. Only the 71 retained
    quotient representatives and an attaining blank-start witness remain. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms raw121_parent_present
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent38Canonical71Raw121
