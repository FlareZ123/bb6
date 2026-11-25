import Canonical74Raw107Raw114Raw117Raw112RosterOnly
import Raw110ParentLateCover
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical73Raw110

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- Remove the raw110 parent using its complete original-source weighted
    cover. Its two late halting leaves require the stronger score 6,766,859. -/
noncomputable def roster :=
  graftRoster BB6.Agent7Raw110.p110 []
    BB6.Agent31Canonical74RosterOnly.roster

/-- The exact raw110 parent is still present after the raw107/raw114/raw117/
    raw112 cuts, so this graft removes one further canonical representative. -/
theorem raw110_parent_present :
    ∃ e ∈ BB6.Agent31Canonical74RosterOnly.roster,
      sameTable e.2 BB6.Agent7Raw110.p110 = true := by
  have h : BB6.Agent31Canonical74RosterOnly.roster.any
      (fun e => sameTable e.2 BB6.Agent7Raw110.p110) = true := by
    decide
  obtain ⟨e, he, hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e, he, hcheck⟩

theorem count : roster.length = 73 := by
  decide

/-- The raw107/raw114/raw117/raw112 dichotomy lifts to the raw110 target,
    and the complete raw110 parent cover removes exactly its matching orbit. -/
theorem sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := BB6.Agent7Raw110.p110)
    (replacement := [])
    (roster := BB6.Agent31Canonical74RosterOnly.roster)
    BB6.Agent7Raw110.p110_root
  · intro m hm
    rcases BB6.Agent31Canonical74RosterOnly.sound m hm with hb | hres
    · exact Or.inl (by
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide))
    · exact Or.inr hres
  · intro m hm
    exact Or.inl
      (BB6.Agent7Raw110.raw110_cover 6766859 (by omega) m hm)

/-- Conditional exactness: all 73 remaining quotient representatives must
    still be covered at B, and the published champion supplies attainment. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms raw110_parent_present
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent47Canonical73Raw110
