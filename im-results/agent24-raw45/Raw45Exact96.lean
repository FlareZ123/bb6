import Raw45CutAssembled
import Raw45Sharp96Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Exact96
open BB6Coverage
open BB6.Agent24Raw45FullChild
open BB6.Agent24Raw45Sharp96

/-- The explicit 96-step halting machine agrees with all seven defined
    instructions of the exact Raw45 five-hole partial parent. -/
theorem witness_fits :
    compatible BB6.Agent24Raw45FullChild.parent witness := by
  intro slot v hv
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;>
    simp [BB6.Agent24Raw45FullChild.parent,witness] at hv ⊢
  all_goals assumption

/-- An exact local weighted maximum: every compatible six-state
    completion scores at most 96, and a compatible machine scores 96. -/
theorem exact_weighted_96 :
    (∀ m : Machine,
      compatible BB6.Agent24Raw45FullChild.parent m → WeightedBound 96 m)
    ∧
    (∃ m : Machine, compatible BB6.Agent24Raw45FullChild.parent m
      ∧ ¬ WeightedBound 95 m) := by
  constructor
  · exact BB6.Agent24Raw45FullChild.weighted_bound
  · exact ⟨witness,witness_fits,excludes_bound_95⟩

#print axioms witness_fits
#print axioms exact_weighted_96
end BB6.Agent24Raw45Exact96
