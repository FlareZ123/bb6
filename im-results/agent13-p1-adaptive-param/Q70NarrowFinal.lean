import Q70NarrowNodes
import AffineParamRoot
namespace BB6.Agent13Narrow
open BB6.Agent13AdaptiveParam

theorem q70root0 (r : Nat) :
    (0,12*(70+P70*r)+4) ∈ BB6.Agent9Adaptive.decode r q70nodes0 := by
  apply List.mem_map.mpr
  refine ⟨(0,844,12*P70,3), ?_, ?_⟩
  · decide
  · change (0,844+12*P70*r)=(0,12*(70+P70*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

theorem q70root1 (r : Nat) :
    (0,10*(70+P70*r)+4) ∈ BB6.Agent9Adaptive.decode r q70nodes1 := by
  apply List.mem_map.mpr
  refine ⟨(0,704,10*P70,7), ?_, ?_⟩
  · decide
  · change (0,704+10*P70*r)=(0,10*(70+P70*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

/-- Exact genuine P1 blank-start critical exclusion for the strengthened
    q=70+2^56*r cylinder, n=1122+2^60*r. -/
theorem critical_1122_mod_2pow60_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(70+P70*r)+2)-2*(16*(70+P70*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    7 57 70 P70 (by decide) (by decide)
    q70nodes0 q70nodes1 q70check0 q70check1 q70root0 q70root1 r

#print axioms critical_1122_mod_2pow60_unreachable
end BB6.Agent13Narrow
