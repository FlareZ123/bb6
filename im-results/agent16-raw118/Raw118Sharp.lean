import Raw118Base
import Raw118Late439
import ResidualAccounted

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw118
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover

/-- The packed first-hole certificate attains the candidate parent score. -/
theorem parent_attained : ∃ m, compatible parent m ∧ HaltsAfter m 756495 := by
  obtain ⟨m, hm, hh⟩ := BB6.Agent16Raw118Late.M439.longAttained
  exact ⟨m, subtable_sound
    (by decide : subtable parent BB6.Agent16Raw118Late.M439.table = true) hm, hh⟩

/-- Every universal weighted parent cover has score at least 756496. -/
theorem parent_min_weighted_bound {B : Nat} (h : Cover (WeightedBound B) parent) :
    bound ≤ B := by
  obtain ⟨m, hm, hh⟩ := parent_attained
  have hd : 0 ∈ delays (zeroNext m) 0 := by
    apply List.mem_filter.mpr
    refine ⟨by decide, List.any_eq_true.mpr ?_⟩
    exact ⟨0, List.mem_finRange 0, by rfl⟩
  exact h.sound m hm 756495 0 hh hd

#print axioms parent_attained
#print axioms parent_min_weighted_bound
end BB6.Agent16Raw118
