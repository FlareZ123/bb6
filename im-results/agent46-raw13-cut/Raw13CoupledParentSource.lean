import Raw13CoupledParent
import Agent46Raw13UpstreamSource

namespace BB6.Agent46Raw13CoupledParent
open BB6Coverage BB6.Agent13BlankDelay

theorem literal_published_eq : published = BB6.Agent46Raw13UpstreamSource.candidate2 := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem unconditional_bound (m : Machine) (hm : compatible parent m) :
    WeightedBound 134 m :=
  bound (literal_published_eq.symm ▸ BB6.Agent46Raw13UpstreamSource.candidate_never2) m hm

#print axioms unconditional_bound
end BB6.Agent46Raw13CoupledParent
