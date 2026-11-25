import CanonicalFrontier
import Combined106Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical78
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier

noncomputable def roster : List (List Move × PartialMachine) :=
  canonicalRemainingRoster.filter fun e => !(BB6.Agent47Combined106.covered e.2)

theorem roster_count : roster.length = 78 := by
  decide

/-- First canonicalize state introduction in the actual rooted tree, then
    consume all eighteen independently source-audited cylinder certificates.
    The surviving obligation is quotient compatibility, not raw equality. -/
theorem roster_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  rcases canonicalRemaining_sound m hm with hb | ⟨entry, he, hq⟩
  · exact Or.inl (by intro k d hk hd; exact Nat.le_trans (hb k d hk hd) (by decide))
  · cases hc : BB6.Agent47Combined106.covered entry.2 with
    | true =>
        rcases hq with ⟨perm, hp, hcomp⟩
        have hz := firstOne_terminal BB6.Agent50TNFPilot.root rfl m hm
        exact Or.inl (weighted_rename_back 7014 perm m hp hz
          (BB6.Agent47Combined106.covered_sound entry.2 hc _ hcomp))
    | false =>
        exact Or.inr ⟨entry, List.mem_filter.mpr ⟨he, by simp [hc]⟩, hq⟩

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
#print axioms roster_sound
#print axioms cover_at_target
#print axioms exact_at_target

end BB6.Agent47Canonical78
