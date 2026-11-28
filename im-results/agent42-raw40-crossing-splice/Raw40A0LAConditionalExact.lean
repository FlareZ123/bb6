import Raw40A0LABase
import Raw40A0LA0REWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LAConditionalExact
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent19Raw40.A0LA

/-- The exact-score successor to the already source-defined canonical
    twelve-child decomposition. The authentic 22,168-step blank witness
    removes the need for an additional attainment hypothesis.

    This theorem is explicitly conditional on all twelve five-hole child
    universal bounds. The hypotheses are NOT discharged here, so it
    does not close the six-hole parent or reduce the global BB6 roster. -/
theorem exact_if_all_children
    (hc : ∀ e ∈ bounds, ∀ m, TNFQuotientCompatible (child e.1) m →
       WeightedBound e.2 m) :
    (∀ m, compatible p m → WeightedBound 22169 m) ∧
    (∀ B < 22169, ∃ m, compatible p m ∧ ¬ WeightedBound B m) := by
  refine ⟨?_,?_⟩
  · intro m hm
    exact close hc m (compatible_quotient hm)
  · intro B hB
    exact BB6.Agent42Raw40A0LA0REWitness.lower_sharp B hB

#print axioms exact_if_all_children
end BB6.Agent42Raw40A0LAConditionalExact
