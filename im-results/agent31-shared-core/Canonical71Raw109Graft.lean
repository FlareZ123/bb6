import Canonical72Raw121Graft
import Raw109Cut
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical71Raw109

open BB6Coverage BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The source-accepted Raw109 parent is still represented after the
    raw107/raw114/raw117/raw112/raw110/raw121 cuts. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent38Canonical72Raw121.roster,
      sameTable e.2 BB6.Agent4Raw109Cut.parent = true := by
  decide

/-- The Raw109 parent root is the required first-write 1RB transition. -/
theorem parent_root :
    BB6.Agent4Raw109Cut.parent initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Graft Raw109 onto the 72-entry Raw121 roster. -/
noncomputable def roster :=
  graftRoster BB6.Agent4Raw109Cut.parent []
    BB6.Agent38Canonical72Raw121.roster

/-- Raw109 removes exactly one further canonical representative. -/
theorem count : roster.length = 71 := by
  decide

/-- The 71-entry quotient roster is sound, assuming the already source-
    accepted Raw109 parent bound 1703. -/
theorem sound
    (raw109 : ∀ m, compatible BB6.Agent4Raw109Cut.parent m →
      WeightedBound 1703 m) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := BB6.Agent4Raw109Cut.parent)
    (replacement := [])
    (roster := BB6.Agent38Canonical72Raw121.roster)
    parent_root
  · intro m hm
    rcases BB6.Agent38Canonical72Raw121.sound m hm with hb | hres
    · exact Or.inl (by
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide))
    · exact Or.inr hres
  · intro m hm
    exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (raw109 m hm k d hk hd) (by decide))

/-- Conditional exactness after the Raw109 graft. The Raw109 parent bound
    is an explicit premise so this interface can be source-checked against
    the shared canonical core independently of its large child closure. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (raw109 : ∀ m, compatible BB6.Agent4Raw109Cut.parent m →
      WeightedBound 1703 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : RawMachine, HaltsAt (tickRaw m) B) :
    ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound raw109) hLeaves champ

#print axioms parent_present
#print axioms parent_root
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent31Canonical71Raw109
