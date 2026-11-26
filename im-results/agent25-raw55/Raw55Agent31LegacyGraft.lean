import Raw55Cut
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw55Agent31LegacyGraft
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent19CanonicalPartial
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier
open BB6.Agent50TNFPilot
abbrev raw55Parent : PartialMachine := BB6.Agent25Raw55Cut.parent
/-- Remove the exact Raw55 parent from Agent31's older concrete 124-entry roster. -/
noncomputable def remainingRootRosterWithoutRaw55 :
    List (List Move × PartialMachine) :=
  remainingRootRoster.filter fun e => !(sameTable e.2 raw55Parent)
/-- The D1=0RE Raw55 parent is present in Agent31's 124-entry root roster. -/
theorem raw55_in_remainingRootRoster :
    remainingRootRoster.any (fun e => sameTable e.2 raw55Parent) = true := by decide
theorem remainingRootRosterWithoutRaw55_count :
    remainingRootRosterWithoutRaw55.length = 123 := by decide
theorem refinedResidualCount :
    remainingRootRosterWithoutRaw55.length + BB6.Agent25Raw55Cut.canonicalRemaining.length = 397 := by decide
/-- Legacy 124-entry roster refinement; the current global consumer is Canonical64. -/
theorem remainingRootRoster_refined_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨
        (∃ e ∈ remainingRootRosterWithoutRaw55, compatible e.2 m) ∨
        (∃ e ∈ BB6.Agent25Raw55Cut.canonicalRemaining,
          TNFQuotientCompatible e.2 m) := by
  intro m hm
  rcases remainingRootRoster_sound_7014 m hm with hbound | ⟨e,he,hcomp⟩
  · exact Or.inl hbound
  · cases hs : sameTable e.2 raw55Parent with
    | false =>
        exact Or.inr (Or.inl ⟨e, List.mem_filter.mpr ⟨he, by simp [hs]⟩, hcomp⟩)
    | true =>
        have heq : e.2 = raw55Parent := sameTable_sound hs
        have hcomp' : compatible raw55Parent m := by simpa [heq] using hcomp
        rcases BB6.Agent25Raw55Cut.canonical_local_sound_84 m
            (compatible_quotient hcomp') with hbound84 | hres
        · exact Or.inl (by
            intro k d hk hd
            exact Nat.le_trans (hbound84 k d hk hd) (by decide))
        · exact Or.inr (Or.inr hres)
#print axioms raw55_in_remainingRootRoster
#print axioms remainingRootRosterWithoutRaw55_count
#print axioms refinedResidualCount
#print axioms remainingRootRoster_refined_sound
end BB6.Agent25Raw55Agent31LegacyGraft
