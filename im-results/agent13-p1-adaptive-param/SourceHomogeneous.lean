import FixedDepthGeneral
import ZeroDepthSource
namespace BB6.Agent13RootHomogeneous
open BB6.Agent13ZeroDepth
open BB6.Agent13FixedDepth

/-- From a genuine P1 feeder-0 shadow node no infinite predecessor ray can
    repeat a single fixed dyadic depth, including zero. -/
theorem source_feeder0_no_homogeneous_ray (q m z t : Nat)
    (hp : BB6.Precision.ShadowReach (16*q+8) (12*q+4) m z)
    (hall : ∀ N : Nat, if t=0 then RunZero (16*q+8) N m z
         else RunFixed (16*q+8) t N m z) : False := by
  by_cases ht : t=0
  · have hzero : ∀N, RunZero (16*q+8) N m z := by
      intro N
      simpa [ht] using hall N
    exact source_p1_feeder0_no_zero_ray q m z hp hzero
  · have hpositive:1≤t := by omega
    have hfixed : ∀N,RunFixed (16*q+8) t N m z := by
      intro N
      simpa [ht] using hall N
    exact no_infinite_fixed_depth (16*q+8) t m z hpositive hfixed

/-- The original-source all-depth result for feeder 1. -/
theorem source_feeder1_no_homogeneous_ray (q m z t : Nat)
    (hp : BB6.Precision.ShadowReach (16*q+9) (10*q+4) m z)
    (hall : ∀ N : Nat, if t=0 then RunZero (16*q+9) N m z
         else RunFixed (16*q+9) t N m z) : False := by
  by_cases ht : t=0
  · have hzero : ∀N, RunZero (16*q+9) N m z := by
      intro N
      simpa [ht] using hall N
    exact source_p1_feeder1_no_zero_ray q m z hp hzero
  · have hpositive:1≤t := by omega
    have hfixed : ∀N,RunFixed (16*q+9) t N m z := by
      intro N
      simpa [ht] using hall N
    exact no_infinite_fixed_depth (16*q+9) t m z hpositive hfixed

#print axioms source_feeder0_no_homogeneous_ray
#print axioms source_feeder1_no_homogeneous_ray
end BB6.Agent13RootHomogeneous
