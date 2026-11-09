import PrefixCylinder
import CrossFeederAll

/-!
# Global uniqueness of infinite source inverse-depth coding for P1 feeders

Combines same-family 2-adic separation of original P1 roots with cross-family
odd-offset finite-state disjointness. Any infinite depth sequence, if it can
be traced from an original feeder root, determines its feeder side and the
natural feeder parameter uniquely.
-/

namespace BB6.Agent9CrossFeeder
open BB6.Precision

def feederL : Bool → Nat → Nat
  | false, q => 16*q+8
  | true, q => 16*q+9

def feederRoot : Bool → Nat → Nat
  | false, q => 12*q+4
  | true, q => 10*q+4

/-- The complete original two-feeder family is injectively coded by every
possible infinite source inverse-depth sequence. -/
theorem infinite_feeder_code_unique
    (side0 side1 : Bool) (q0 q1 : Nat)
    (p0 : InfiniteShadowPath (feederL side0 q0) (feederRoot side0 q0))
    (p1 : InfiniteShadowPath (feederL side1 q1) (feederRoot side1 q1))
    (hm0 : p0.m 0=0) (hz0 : p0.z 0=feederRoot side0 q0)
    (hm1 : p1.m 0=0) (hz1 : p1.z 0=feederRoot side1 q1)
    (hsame : ∀ n, p0.depth n=p1.depth n) :
    side0=side1 ∧ q0=q1 := by
  cases side0 <;> cases side1
  · constructor
    · rfl
    · exact feeder12_depth_sequence_parameter_unique q0 q1 p0 p1 hm0 hz0 hm1 hz1 hsame
  · exact False.elim (no_common_cross_feeder_depth_stream q0 q1 p0 p1 hm0 hm1 hsame)
  · exact False.elim (no_common_cross_feeder_depth_stream q1 q0 p1 p0 hm1 hm0 (fun n => (hsame n).symm))
  · constructor
    · rfl
    · exact feeder10_depth_sequence_parameter_unique q0 q1 p0 p1 hm0 hz0 hm1 hz1 hsame

#print axioms infinite_feeder_code_unique
end BB6.Agent9CrossFeeder
