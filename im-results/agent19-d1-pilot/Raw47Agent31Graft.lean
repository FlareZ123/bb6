import Raw47Cut
import FourHoleResidualRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw47Agent31Graft
open BB6Coverage
open BB6.Agent19Raw47Cut
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier
open BB6.Agent47RootedTNF
open BB6.Agent50TNFPilot

/-- Remove every concrete roster entry with the Raw47 partial table. -/
noncomputable def remainingRootRosterWithoutRaw47 :
    List (List Move × PartialMachine) :=
  remainingRootRoster.filter fun e => !(sameTable e.2 parent)

/-- The D1=0RC Raw47 parent is present in Agent31's current 124-entry roster. -/
theorem raw47_in_remainingRootRoster :
    remainingRootRoster.any (fun e => sameTable e.2 parent) = true := by decide

/-- Exactly one roster entry is replaced by the Raw47 quotient refinement. -/
theorem remainingRootRosterWithoutRaw47_count :
    remainingRootRosterWithoutRaw47.length = 123 := by decide

/-- Agent31's concrete firstOne roster, with Raw47 replaced by its 114
    source-checked quotient residuals. This is a strict, source-sound
    refinement in the existing B=7014 roster interface. -/
theorem remainingRootRoster_refined_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨
        (∃ e ∈ remainingRootRosterWithoutRaw47, compatible e.2 m) ∨
        (∃ e ∈ canonicalRemaining, TNFQuotientCompatible e.2 m) := by
  intro m hm
  rcases remainingRootRoster_sound_7014 m hm with hbound | ⟨e,he,hcomp⟩
  · exact Or.inl hbound
  · cases hs : sameTable e.2 parent with
    | false =>
        exact Or.inr (Or.inl ⟨e, List.mem_filter.mpr ⟨he, by simp [hs]⟩, hcomp⟩)
    | true =>
        have heq : e.2 = parent := sameTable_sound hs
        have hcomp' : compatible parent m := by simpa [heq] using hcomp
        rcases canonical_local_sound_84 m (compatible_quotient hcomp') with hbound84 | hres
        · exact Or.inl (by
            intro k d hk hd
            exact Nat.le_trans (hbound84 k d hk hd) (by decide))
        · exact Or.inr (Or.inr hres)

#print axioms raw47_in_remainingRootRoster
#print axioms remainingRootRosterWithoutRaw47_count
#print axioms remainingRootRoster_refined_sound
end BB6.Agent19Raw47Agent31Graft
