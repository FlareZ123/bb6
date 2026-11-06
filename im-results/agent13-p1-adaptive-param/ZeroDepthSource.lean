import ZeroDepth
import UniformPrecisionPath
namespace BB6.Agent13ZeroDepth

/-- Transport a genuine original-source scalar inverse path into the
    mathematical shadow margin invariant, without changing the edge law. -/
theorem original_shadow_slack_four (L root m z : Nat)
    (hroot:root+4≤L)
    (h : BB6.Precision.ShadowReach L root m z) :
    z+4≤L+m := by
  have hi : ShadowReach L root m z := by
    induction h with
    | root => exact ShadowReach.root
    | @step m z hp t v zp hd hn ih =>
        exact ShadowReach.step ih t v zp hd hn
  exact shadow_slack_four L root m z hroot hi

/-- Source-authentic P1 feeder L0 has permanent scalar margin four. -/
theorem source_p1_feeder0_margin (q m z : Nat)
    (hp : BB6.Precision.ShadowReach (16*q+8) (12*q+4) m z) :
    z+4≤16*q+8+m := by
  exact original_shadow_slack_four (16*q+8) (12*q+4) m z
    (by omega) hp

/-- Source-authentic P1 feeder L1 has permanent scalar margin four. -/
theorem source_p1_feeder1_margin (q m z : Nat)
    (hp : BB6.Precision.ShadowReach (16*q+9) (10*q+4) m z) :
    z+4≤16*q+9+m := by
  exact original_shadow_slack_four (16*q+9) (10*q+4) m z
    (by omega) hp

/-- From any genuine source P1 feeder-shadow node, arbitrarily long
    consecutive depth-zero predecessor sequences are impossible. -/
theorem source_p1_feeder0_no_zero_ray (q m z : Nat)
    (hp : BB6.Precision.ShadowReach (16*q+8) (12*q+4) m z)
    (hall : ∀ N : Nat, RunZero (16*q+8) N m z) : False := by
  exact no_infinite_zero_depth (16*q+8) m z
    (source_p1_feeder0_margin q m z hp) hall

theorem source_p1_feeder1_no_zero_ray (q m z : Nat)
    (hp : BB6.Precision.ShadowReach (16*q+9) (10*q+4) m z)
    (hall : ∀ N : Nat, RunZero (16*q+9) N m z) : False := by
  exact no_infinite_zero_depth (16*q+9) m z
    (source_p1_feeder1_margin q m z hp) hall

#print axioms original_shadow_slack_four
#print axioms source_p1_feeder0_no_zero_ray
#print axioms source_p1_feeder1_no_zero_ray
end BB6.Agent13ZeroDepth
