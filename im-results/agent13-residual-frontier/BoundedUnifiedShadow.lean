import BoundedShadow
import UnifiedShadow
import Lean.Elab.Tactic.Omega
namespace BB6.Agent13BoundedUnified
open BB6.Agent13BoundedShadow BB6.Agent13UnifiedShadow BB6.Agent13NegativeShadow
def unifiedBounded (b j m : Nat) : Bool := unifiedCheckWith bounded b j m

theorem bounded_stop_cylinder_excluded (b j0 m0 j m k : Nat)
    (h : unifiedBounded b j0 m0=true)
    (hjj : j0≤j) (hmm : m0≤m) (hb : b≤2*m+2)
    (hjcon : 2^b∣j-j0) (hmcon : 2^b∣m-m0)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) :
    ¬ BB6.Agent3.CReach (2*j+1) k :=
  unified_cylinder_exclusion_with BB6.Agent3.CReach source_parent_of_right_ge8
    BB6.Agent13TwoParent.odd_forbidden_image bounded
    (fun b x y s h hc => bounded_sound BB6.Agent3.CReach
      (fun x y _ hy => source_parent_of_right_ge8 x y hy)
      BB6.Agent13TwoParent.odd_forbidden_image b x y s h hc)
    b j0 m0 j m k h hjj hmm hb hjcon hmcon hstop

theorem bounded_stop_excluded (j m k : Nat)
    (h : unifiedBounded (2*m+2) j m=true)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) :
    ¬ BB6.Agent3.CReach (2*j+1) k :=
  bounded_stop_cylinder_excluded (2*m+2) j m j m k h
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by simp) (by simp) hstop

#print axioms bounded_stop_cylinder_excluded
#print axioms bounded_stop_excluded
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#eval ((List.range 1000).filter (fun m => !unifiedBounded (2*m+2) 0 m))
end BB6.Agent13BoundedUnified
