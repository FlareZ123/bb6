import RayNonFork
import RayDepthResidue
set_option maxHeartbeats 0

namespace CascadeRayDepthPhysical
open CascadeRayDepthResidue CascadeRayDepthHensel CascadeRayPeriod CascadeOddRay CascadeFiveForced

/-- Every physically admissible high-band ray height inherits the full
    unique ternary valuation depth residue, with the nonnegativity guard. -/
theorem admissible_ray_valuation_iff (n j k : Nat)
    (hn : n%6=4 ∨ n%6=5) (hlarge : 4≤n)
    (hband : deficit n j≤2^n) :
    ((3:Int)^(k+1) ∣ (2*ray n j+5:Int)) ↔
    j%depthPeriod k=depthResidue n k := by
  rw [←signed_ray_eq_numerator n j hlarge hband]
  exact depthResidue_iff n k j hn

/-- Outside the computable unique nine-divisibility depth, the genuine
    blank-root inverse height has exactly one forced source reset parent. -/
theorem residue_nonfork_root_iff (n j : Nat)
    (hn : n%6=4 ∨ n%6=5) (hlarge : 4≤n)
    (hband : deficit n j≤2^n)
    (hoff : j%depthPeriod 1 ≠ depthResidue n 1) :
    CascadeSweep.ReachC (2,0) (ray n j,0) ↔
    CascadeSweep.ReachC (2,0) (ray n (j+1),0) := by
  have hmod : signedZ n j%9≠0 := by
    intro hzero
    have hdvd : (3:Int)^2 ∣ signedZ n j := by
      apply Int.dvd_iff_emod_eq_zero.mpr
      simpa using hzero
    exact hoff ((depthResidue_iff n 1 j hn).mp hdvd)
  exact nonfork_root_iff n j hlarge hband hmod

#print axioms residue_nonfork_root_iff
#print axioms admissible_ray_valuation_iff
end CascadeRayDepthPhysical
