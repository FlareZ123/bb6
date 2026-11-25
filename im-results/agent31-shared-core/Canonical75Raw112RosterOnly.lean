import CanonicalTwoParentRosterOnly
import Raw112ClosedCover
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical75Raw112RosterOnly

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- Remove the raw112 parent from the two-parent quotient roster. -/
noncomputable def roster :=
  BB6.Agent47CanonicalTwoParent.roster76.filter
    (fun e => !(sameTable e.2 BB6.Agent47Raw112.parent))

/-- The raw112 parent is an actual entry of the 76-residual partition. -/
theorem raw112_parent_present :
    ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      sameTable e.2 BB6.Agent47Raw112.parent = true := by
  decide

/-- The source-accepted raw112 parent cover removes exactly one residual. -/
theorem count : roster.length = 75 := by
  decide

/-- Mixed-bound composition: the 7014 root branch lifts to 100000, and the
    raw112 parent branch is discharged by its original-source Cover. -/
theorem sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 100000 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound m hm with hb | ⟨e, he, perm, hfix, hcomp⟩
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 BB6.Agent47Raw112.parent = true
    · have heq := sameTable_sound hmatch
      have hc : compatible BB6.Agent47Raw112.parent (renameTable perm m) := heq ▸ hcomp
      have hb' := BB6.Agent47Raw112.parent_cover.sound (renameTable perm m) hc
      have hz := firstOne_terminal BB6.Agent47Raw112.parent
        BB6.Agent47Raw112.parent_root (renameTable perm m) hc
      exact Or.inl (weighted_rename_back 100000 perm m hfix
        (zeroNext_none_rename_iff perm m hfix).mp hz hb')
    · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [roster, hmatch]⟩,
        perm, hfix, hcomp⟩

/-- Conditional exactness at every target B>=100000; all 75 retained Covers
    and an attaining blank-start witness remain explicit premises. -/
theorem exact_at_target (B : Nat) (hB : 100000 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms raw112_parent_present
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent31Canonical75Raw112RosterOnly
