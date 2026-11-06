import Q89NarrowNodes
import AffineParamRoot
namespace BB6.Agent13Narrow
open BB6.Agent13AdaptiveParam

theorem q89root0 (r : Nat) :
    (0,12*(89+P*r)+4) ∈ BB6.Agent9Adaptive.decode r q89nodes0 := by
  apply List.mem_map.mpr
  refine ⟨(0,1072,12*P,5), ?_, ?_⟩
  · decide
  · change (0,1072+12*P*r)=(0,12*(89+P*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

theorem q89root1 (r : Nat) :
    (0,10*(89+P*r)+4) ∈ BB6.Agent9Adaptive.decode r q89nodes1 := by
  apply List.mem_map.mpr
  refine ⟨(0,894,10*P,2), ?_, ?_⟩
  · decide
  · change (0,894+10*P*r)=(0,10*(89+P*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

/-- Exact genuine P1 blank-start critical exclusion for the strengthened
    q=89+2^50*r cylinder, n=1426+2^54*r. -/
theorem critical_1426_mod_2pow54_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(89+P*r)+2)-2*(16*(89+P*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    11 51 89 P (by decide) (by decide)
    q89nodes0 q89nodes1 q89check0 q89check1 q89root0 q89root1 r

#print axioms critical_1426_mod_2pow54_unreachable
end BB6.Agent13Narrow
