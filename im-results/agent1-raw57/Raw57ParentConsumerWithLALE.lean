import Raw57ParentConsumer
import Raw57LA1Data
import Raw57LE1Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57ConsumerWithLALE

open BB6Coverage BB6.Agent13BlankDelay

/-- The two source-accepted residual children 1LA and 1LE are discharged
    internally. Only 1LB, 0LF and 1LF remain as parent-Cover hypotheses. -/
theorem cover_at_target_from_three (B : Nat) (hB : 1613 ≤ B)
    (hLB : Cover (WeightedBound B)
      (BB6.Agent1Raw57Parent.child ⟨true,false,1⟩))
    (h0LF : Cover (WeightedBound B)
      (BB6.Agent1Raw57Parent.child ⟨false,false,5⟩))
    (h1LF : Cover (WeightedBound B)
      (BB6.Agent1Raw57Parent.child ⟨true,false,5⟩)) :
    Cover (WeightedBound B) BB6.Agent1Raw57Parent.parent := by
  have hLA : ∀ m,
      compatible (BB6.Agent1Raw57Parent.child ⟨true,false,0⟩) m →
      WeightedBound 1613 m :=
    BB6.Agent1Raw57LA1.all_completions
  have hLE : Cover (WeightedBound B)
      (BB6.Agent1Raw57Parent.child ⟨true,false,4⟩) := by
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    exact Nat.le_trans
      (BB6.Agent1Raw57LE1.all_completions m hm k d hk hd)
      (by omega)
  exact BB6.Agent1Raw57Consumer.cover_at_target_from_four
    B (by omega) hLA hLB hLE h0LF h1LF

#print axioms cover_at_target_from_three

end BB6.Agent1Raw57ConsumerWithLALE
