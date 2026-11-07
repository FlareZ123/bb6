import Q853NarrowNodes
import AffineParamRoot

namespace BB6.Agent13Narrow
open BB6.Agent13AdaptiveParam

theorem q853root0 (r : Nat) :
    (0,12*(853+P853*r)+4) ∈ BB6.Agent9Adaptive.decode r q853nodes0 := by
  apply List.mem_map.mpr
  refine ⟨(0,10240,12*P853,12), ?_, ?_⟩
  · decide
  · change (0,10240+12*P853*r)=(0,12*(853+P853*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

theorem q853root1 (r : Nat) :
    (0,10*(853+P853*r)+4) ∈ BB6.Agent9Adaptive.decode r q853nodes1 := by
  apply List.mem_map.mpr
  refine ⟨(0,8534,10*P853,2), ?_, ?_⟩
  · decide
  · change (0,8534+10*P853*r)=(0,10*(853+P853*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

/-- Original blank-start P1 critical-gateway exclusion for every
    q = 853 + 1024*r, equivalently n = 13650 + 16384*r. -/
theorem critical_13650_mod_16384_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(853+P853*r)+2)-2*(16*(853+P853*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 11 853 P853 (by decide) (by decide)
    q853nodes0 q853nodes1 q853check0 q853check1 q853root0 q853root1 r

#print axioms critical_13650_mod_16384_unreachable
end BB6.Agent13Narrow
