import Raw124New1LBCut
import ResidualCover
import Raw124OneLBWide207
import Raw124OneLBWide209
import Raw124OneLBWide212
import Raw124OneLBWide217
import Raw124OneLBWide711
import Raw124OneLB937
import Raw124OneLB980
import Raw124OneLB2083

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124OneLBComplete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover
open BB6.Agent2Raw124New1LB

def seals : List (Accepted 3006) :=
  [nonhalt 3006 BB6.Agent2Raw124OneLBWide.M207.table BB6.Agent2Raw124OneLBWide.M207.never,
   nonhalt 3006 BB6.Agent2Raw124OneLBWide.M209.table BB6.Agent2Raw124OneLBWide.M209.never,
   nonhalt 3006 BB6.Agent2Raw124OneLBWide.M212.table BB6.Agent2Raw124OneLBWide.M212.never,
   nonhalt 3006 BB6.Agent2Raw124OneLBWide.M217.table BB6.Agent2Raw124OneLBWide.M217.never,
   nonhalt 3006 BB6.Agent2Raw124OneLBWide.M711.table BB6.Agent2Raw124OneLBWide.M711.never,
   nonhalt 3006 BB6.Agent2Raw124OneLB937.table BB6.Agent2Raw124OneLB937.never_source,
   nonhalt 3006 BB6.Agent2Raw124OneLB980.table BB6.Agent2Raw124OneLB980.never_source,
   nonhalt 3006 BB6.Agent2Raw124OneLB2083.table BB6.Agent2Raw124OneLB2083.never_source]

theorem no_open : (remaining seals residuals).length = 0 := by decide

/-- Exact weighted upper bound for the entire F1=1LB child of Raw124. -/
theorem bound_all : ∀ m, compatible branch m → WeightedBound 3006 m := by
  intro m hm
  rcases consume seals branch_sound m hm with hb | ⟨e,he,_⟩
  · exact hb
  · have hnil : remaining seals residuals = [] := List.length_eq_zero_iff.mp no_open
    rw [hnil] at he
    simp at he

#print axioms no_open
#print axioms bound_all
end BB6.Agent2Raw124OneLBComplete
