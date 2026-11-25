import Canonical72RosterOnly
import Raw121Data
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Canonical71Raw121RosterOnly

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement

/-- Graft the source-audited Raw121 six-hole cylinder into the 72-entry
    champion-independent roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent11Raw121.p121 []
    BB6.Agent8Canonical72RosterOnly.roster

/-- The Raw121 parent is still present after the raw107/raw114/raw117/
    raw119/raw115/raw113 cuts. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent8Canonical72RosterOnly.roster,
      sameTable e.2 BB6.Agent11Raw121.p121 = true := by
  decide

/-- The additional Raw121 parent removes exactly one further representative. -/
theorem roster_count : roster.length = 71 := by
  decide

/-- Champion-independent 7014 dichotomy after all seven parent cuts. -/
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

/-- Conditional exactness after the Raw121 graft. The 71 retained quotient
    representatives still require Covers at the target score. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms parent_present
#print axioms roster_count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent8Canonical71Raw121RosterOnly
