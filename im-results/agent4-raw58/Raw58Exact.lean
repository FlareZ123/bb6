import Raw58MoreCut2
import Raw58SharpComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw58Exact
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent4Raw58SharpComposition

theorem cut :
    ∀ m, compatible p58 m → WeightedBound 374 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  intro m hm
  have h := BB6.Agent4Raw58MoreCut2.parent_dichotomy m hm
  have hr : BB6.Agent4Raw58MoreCut2.remaining = remaining := by decide
  rw [hr] at h
  exact h

theorem raw58_bound_exact (B : Nat) :
    (∀ m, compatible p58 m → WeightedBound B m) ↔ 3055746 ≤ B :=
  raw58_exact cut B

theorem all_completions : ∀ m, compatible p58 m → WeightedBound 3055746 m :=
  (raw58_bound_exact 3055746).mpr (by decide)

theorem coverRaw58 (B : Nat) (hB : 3055746 ≤ B) : Cover (WeightedBound B) p58 :=
  Cover.leaf p58 ((raw58_bound_exact B).mpr hB)

#print axioms cut
#print axioms raw58_bound_exact
#print axioms all_completions
#print axioms coverRaw58
end BB6.Agent4Raw58Exact
