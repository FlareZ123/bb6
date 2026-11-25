import Raw112Data
import RosterCoverComposition

namespace BB6.Agent47Raw112

open BB6Coverage
open BB6.Agent13BlankDelay

/-- The raw112 partial audit is at 100,000. If each of its two residual
    cylinders is covered at a target B, its parent is covered at B as well.
    This is the mixed-threshold step needed to feed the raw112 parent into
    the canonical roster without weakening the target bound. -/
theorem parent_cover_of_residual_covers {B : Nat}
    (hB : 100000 ≤ B)
    (hLeaves : ∀ e ∈ residuals, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) parent := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases sound m hm with hBound | ⟨e, he, hcompat⟩
  · exact BB6.Agent13RosterComposition.weightedBound_mono_local hB hBound
  · exact (hLeaves e he).sound m hcompat

#print axioms parent_cover_of_residual_covers

end BB6.Agent47Raw112
