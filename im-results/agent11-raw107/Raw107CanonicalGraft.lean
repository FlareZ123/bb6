import Canonical78Roster
import Raw107ParentClosure
import ThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw107Canonical
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

abbrev parent : PartialMachine := BB6.Agent10Raw107Root.parent

def isRaw107 (p : PartialMachine) : Bool :=
  BB6.Agent31ThreeHole.tableOK p parent

noncomputable def roster : List (List Move × PartialMachine) :=
  BB6.Agent47Canonical78.roster.filter fun e => !(isRaw107 e.2)

/-- The raw107 certificate is an additional canonical residual, not an alias
    of any of the eighteen cylinders already consumed by Canonical78. -/
theorem roster_count : roster.length = 77 := by
  decide

theorem raw107_quotient_bound (m : Machine)
    (hq : TNFQuotientCompatible parent m) : WeightedBound 815 m :=
  quotientSafe (by decide) BB6.Agent11Raw107ParentClosure.all_completions m hq

/-- Consume raw107 through the same root-fixing state-renaming transport as
    the existing canonical frontier. Keep every other obligation. -/
theorem roster_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent47Canonical78.roster_sound m hm with hb | ⟨e, he, hq⟩
  · exact Or.inl hb
  · cases hc : isRaw107 e.2 with
    | false =>
      exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [hc]⟩, hq⟩
    | true =>
      have ht : e.2 = parent :=
        BB6.Agent31ThreeHole.tableOK_sound _ _ hc
      have hb := raw107_quotient_bound m (ht ▸ hq)
      exact Or.inl (by intro k d hk hd; exact Nat.le_trans (hb k d hk hd) (by decide))

/-- All 77 remaining covers are needed at the eventual target B. -/
theorem cover_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  cover_of_quotient_roster hB roster_sound hLeaves

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster_sound hLeaves champ

#print axioms roster_count
#print axioms raw107_quotient_bound
#print axioms roster_sound
#print axioms cover_at_target
#print axioms exact_at_target

end BB6.Agent11Raw107Canonical
