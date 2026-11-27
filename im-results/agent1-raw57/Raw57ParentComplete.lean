import Raw57ParentConsumerWithLALE
import Raw57LB1Data
import Raw57LF0Data
import Raw57LF1Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Complete

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent1Raw57Parent

/-- Lift the source-accepted 1LB child Cover from its sharp bound to the
    common Raw57 parent target. -/
theorem lb_cover : Cover (WeightedBound 1613) (child ⟨true,false,1⟩) := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent1Raw57LB1.all_completions m hm k d hk hd)
    (by decide : 806 ≤ 1613)

/-- The 0LF child is already certified at the common target. -/
theorem lf0_cover : Cover (WeightedBound 1613) (child ⟨false,false,5⟩) := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent1Raw57LF0.all_completions m hm k d hk hd)
    (by decide : 1500 ≤ 1613)

/-- The 1LF child is certified at the common target once its source audit
    accepts the complete sibling tree. -/
theorem lf1_cover : Cover (WeightedBound 1613) (child ⟨true,false,5⟩) := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent1Raw57LF1.all_completions m hm k d hk hd)
    (by decide : 1500 ≤ 1613)

/-- Exact Cover of the six-hole Raw57 parent at weighted bound 1613.
    The parent dichotomy consumes all 24 ordinary A1 choices and the
    authentic halt choice; the five nontrivial siblings are all discharged. -/
theorem parent_cover : Cover (WeightedBound 1613) parent := by
  exact BB6.Agent1Raw57ConsumerWithLALE.cover_at_target_from_three
    1613 (by decide) lb_cover lf0_cover lf1_cover

#print axioms lb_cover
#print axioms lf0_cover
#print axioms lf1_cover
#print axioms parent_cover

end BB6.Agent1Raw57Complete
