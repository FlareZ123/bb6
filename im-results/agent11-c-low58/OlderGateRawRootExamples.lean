import HighDyadicOlderGateFast

namespace BB6.Agent11OlderGateFastExamples

open BB6.Agent11OlderGateFast

/-- Three high targets in Agent4's raw-mass-2000 box satisfy the
    original Agent19 older gate at depth n=0. -/
theorem older_gate_witnesses :
    gate 0 14 1 ∧ gate 0 30 1 ∧ gate 0 46 1 := by
  decide

/-- The exact one-candidate evaluator therefore rejects these three
    pairs from the old high-parameter predicate. -/
theorem older_gate_rejects_raw_targets :
    candidateAllowedBool 14 1=false ∧
    candidateAllowedBool 30 1=false ∧
    candidateAllowedBool 46 1=false := by
  exact ⟨
    candidateAllowedBool_false_of_gate 14 1 0 (by decide),
    candidateAllowedBool_false_of_gate 30 1 0 (by decide),
    candidateAllowedBool_false_of_gate 46 1 0 (by decide)⟩

#print axioms older_gate_witnesses
#print axioms older_gate_rejects_raw_targets
end BB6.Agent11OlderGateFastExamples
