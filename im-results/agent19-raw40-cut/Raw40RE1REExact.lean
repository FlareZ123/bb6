import Raw40RE1REAll
import Raw40RE1REWitness
import CanonicalFrontier
namespace BB6.Agent19Raw40.RE1REExact
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
theorem exact_weighted : (∀ m, compatible Raw40RE1RE.p m → WeightedBound 165 m) ∧
    ∀ B < 165, ∃ m, compatible Raw40RE1RE.p m ∧ ¬ WeightedBound B m := by
  refine ⟨Raw40RE1RE.all,?_⟩
  exact RE1REWitness.lower
theorem quotient_bound : ∀ m, TNFQuotientCompatible Raw40RE1RE.p m → WeightedBound 165 m :=
  quotientSafe Raw40RE1RE.root Raw40RE1RE.all
#print axioms exact_weighted
#print axioms quotient_bound
end BB6.Agent19Raw40.RE1REExact
