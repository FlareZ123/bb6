import Canonical71Raw121RosterOnly
import Raw110ParentLateCover
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Canonical70Raw121Raw110RosterOnly

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement

/-- Graft the source-audited raw110 late-parent Cover onto the 71-entry
    Raw121-refined roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent7Raw110.p110 []
    BB6.Agent8Canonical71Raw121RosterOnly.roster

/-- The raw110 parent remains as one exact representative after the Raw121 cut. -/
theorem raw110_parent_present :
    ∃ e ∈ BB6.Agent8Canonical71Raw121RosterOnly.roster,
      sameTable e.2 BB6.Agent7Raw110.p110 = true := by
  decide

/-- The raw110 parent removes exactly one more quotient representative. -/
theorem roster_count : roster.length = 70 := by
  decide

/-- Mixed-bound root dichotomy: the 7014 Raw121 roster lifts to 6766859,
    and the complete raw110 parent Cover removes its matching orbit. -/
theorem sound :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := BB6.Agent7Raw110.p110)
    (replacement := [])
    (roster := BB6.Agent8Canonical71Raw121RosterOnly.roster)
    BB6.Agent7Raw110.p110_root
  · intro m hm
    rcases BB6.Agent8Canonical71Raw121RosterOnly.sound m hm with hb | hres
    · exact Or.inl (by
        intro k d hk hd
        exact Nat.le_trans (hb m hm k d hk hd) (by decide))
    · exact Or.inr hres
  · intro m hm
    exact Or.inl
      (BB6.Agent7Raw110.raw110_cover 6766859 (by omega) m hm)

/-- Conditional exactness: all 70 retained quotient representatives still
    require Covers at B, with an attaining blank-start witness. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms raw110_parent_present
#print axioms roster_count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent8Canonical70Raw121Raw110RosterOnly
