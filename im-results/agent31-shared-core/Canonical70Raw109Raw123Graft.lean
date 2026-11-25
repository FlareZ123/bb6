import Canonical71Raw109Graft
import Raw123Base
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical70Raw109Raw123

open BB6Coverage BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The Raw123 E1=0RF parent remains represented after the Raw109 graft
    into the source-accepted 72-entry Raw121 roster. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent31Canonical71Raw109.roster,
      sameTable e.2 BB6.Agent7Raw123.p123 = true := by
  decide

/-- Raw123 is a member of the standard first-one rooted cylinder. -/
theorem parent_root :
    BB6.Agent7Raw123.p123 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent7Raw123.p123_root

/-- Graft the source-accepted Raw123 parent onto the 71-entry Raw109 roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent7Raw123.p123 []
    BB6.Agent31Canonical71Raw109.roster

/-- Raw123 removes exactly one further canonical representative. -/
theorem count : roster.length = 70 := by
  decide

/-- The 70-entry quotient roster is sound, assuming the independently
    source-accepted Raw109 bound and Raw123 Cover. -/
theorem sound
    (raw109 : ∀ m, compatible BB6.Agent4Raw109Cut.parent m →
      WeightedBound 1703 m)
    (raw123 : Cover (WeightedBound 10000) BB6.Agent7Raw123.p123) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := BB6.Agent7Raw123.p123)
    (replacement := [])
    (roster := BB6.Agent31Canonical71Raw109.roster)
    parent_root
  · intro m hm
    rcases BB6.Agent31Canonical71Raw109.sound raw109 m hm with hb | hres
    · exact Or.inl hb
    · exact Or.inr hres
  · intro m hm
    exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (raw123.sound m hm k d hk hd) (by decide))

/-- Conditional exactness after both additional parent cuts. The Raw109
    bound and Raw123 Cover are explicit premises, so this wrapper can be
    source-audited independently of the two large parent closures. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (raw109 : ∀ m, compatible BB6.Agent4Raw109Cut.parent m →
      WeightedBound 1703 m)
    (raw123 : Cover (WeightedBound 10000) BB6.Agent7Raw123.p123)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : RawMachine, HaltsAt (tickRaw m) B) :
    ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound raw109 raw123) hLeaves champ

#print axioms parent_present
#print axioms parent_root
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent31Canonical70Raw109Raw123
