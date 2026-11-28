import FirstMixedAnchorExclusion
import AnchorEpoch
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321FirstMixedRoot
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent2F321AnchorEpoch
open BB6.Agent2F321Phase6
open BB6.Agent2F321Phase6Bridge

/-- The Equal predecessor of anchor (19,173,934,1) would be
    (9,586,965,9,586,965), which violates the all-depth root Phase6
    invariant. -/
theorem first_mixed_equal_predecessor_unreachable
    {n : Nat}
    (hr : CounterReach 1 1 n 9586965 9586965) :
    False := by
  have hp := counterReach_phase6 hr
  rcases hp with hseed | hp
  · omega
  · unfold Phase6 at hp
    rcases hp with h01 | h02 | h15 <;> omega

/-- The concrete source-faithful H^22/F terminal anchor can never be a
    small-second anchor on the authentic root orbit.  Equal and MiddleOdd are
    its only AnchorMove possibilities; both are now eliminated. -/
theorem first_mixed_anchor_not_root_anchor
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : AnchorMove a d 19173934 1) :
    False := by
  unfold AnchorMove at ha
  rcases ha with hE | hM
  · rcases hE with ⟨had,hR,hc⟩
    subst d
    have haeq : a=9586965 := by omega
    subst a
    exact first_mixed_equal_predecessor_unreachable hr
  · rcases hM with hEven | hOdd
    · rcases hEven with ⟨h1,h2,hp,hR,hc⟩
      omega
    · rcases hOdd with ⟨h1,h2,hp,hR,hc⟩
      exact first_mixed_anchor_middleOdd_predecessor_unreachable
        hr hR h1 h2

#print axioms first_mixed_equal_predecessor_unreachable
#print axioms first_mixed_anchor_not_root_anchor
end BB6.Agent31F321FirstMixedRoot
