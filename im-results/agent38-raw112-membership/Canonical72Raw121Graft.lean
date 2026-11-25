import Canonical73Raw110Composition
import Raw121Data
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Canonical72Raw121

open BB6Coverage BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The Raw121 parent remains represented after the raw107/raw114/raw117/
    raw112/raw110 cuts defining the canonical73 roster. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent47Canonical73Raw110.roster,
      sameTable e.2 BB6.Agent11Raw121.p121 = true := by
  decide

/-- Graft the source-audited Raw121 parent onto the 73-entry roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent11Raw121.p121 []
    BB6.Agent47Canonical73Raw110.roster

/-- The additional Raw121 cut removes exactly one representative. -/
theorem count : roster.length = 72 := by
  decide

/-- The 72-entry roster inherits the 6,766,859 root dichotomy. -/
theorem sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := BB6.Agent11Raw121.p121)
    (replacement := [])
    (roster := BB6.Agent47Canonical73Raw110.roster)
    BB6.Agent11Raw121.p121_root
  · intro m hm
    rcases BB6.Agent47Canonical73Raw110.sound m hm with hb | hres
    · exact Or.inl (by
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide))
    · exact Or.inr hres
  · intro m hm
    exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans
        (BB6.Agent11Raw121.all121 m hm k d hk hd)
        (by decide))

/-- Conditional exactness: all 72 retained quotient Covers and an attaining
    blank-start witness remain explicit premises. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms BB6.Agent11Raw121.all121
#print axioms parent_present
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent38Canonical72Raw121
