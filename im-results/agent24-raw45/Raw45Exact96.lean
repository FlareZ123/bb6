import Raw45CutAssembled
import Raw45Sharp96Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Exact96
open BB6Coverage BB6.Agent13BlankDelay
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

/-- The empty path from initial state A witnesses blank-entry delay zero,
    regardless of the unknown transitions of the completed machine. -/
private theorem zero_delay_all (m : Machine) :
    0 ∈ delays (zeroNext m) 0 := by decide

/-- Every genuinely halting compatible completion stops within 96
    instructions, including its final halting transition. -/
theorem all_halting_scores_le_96 :
    ∀ m : Machine, compatible BB6.Agent24Raw45FullChild.parent m →
      ∀ n, HaltsAfter m n → n+1 ≤ 96 := by
  intro m hm n hn
  have hb := weighted_bound m hm n 0 hn (zero_delay_all m)
  omega

/-- Exact ordinary blank-step maximum over all 25^5 completions of
    this five-hole source machine: attained at exactly 96 steps,
    while all other halting completions stop in at most 96. -/
theorem exact_blank_step_96 :
    (∀ m : Machine, compatible BB6.Agent24Raw45FullChild.parent m →
      ∀ n, HaltsAfter m n → n+1 ≤ 96)
    ∧ (∃ m : Machine, compatible BB6.Agent24Raw45FullChild.parent m
      ∧ HaltsAfter m 95) :=
  ⟨all_halting_scores_le_96,⟨witness,witness_fits,halts_after_95⟩⟩

#print axioms all_halting_scores_le_96
#print axioms exact_blank_step_96
end BB6.Agent24Raw45Exact96
