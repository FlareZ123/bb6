import ShadowGraphBridge
import ShadowFeederRoots
namespace BB6.Shadow
open BB6.Agent1Quarter

/-- Every bounded authentic L0 P1 odd feeder state is in the graph
    rooted at (m,z)=(0,12q+4) with its exact source coefficient. -/
theorem bounded_l0_cone_in_shadow_graph
    (q u b d m : Nat)
    (hu : u+4*q+3=7*2^(16*q)) (hu1 : 1≤u)
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0) (hcost : m+2≤16*q) :
    ∃ (w z alpha : Nat),
      ShadowReach (16*q+8) (12*q+4) m z ∧
      0<z ∧ 4≤w ∧ (16*q+8)+m=w+z ∧
      2^m*(b+4*w)=alpha*2^(16*q) := by
  obtain ⟨hmass,henc,_,_⟩ := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  exact bounded_odd_cone_in_shadow_graph (16*q) (16*q+8)
    (4*u-4) (4*u+9) (4*q+4) (12*q+4) 28
    hmass (by omega) (by omega) (by omega) (by omega) henc
    b d m hcone hmod hcost

/-- Every bounded authentic L1 P1 odd feeder state is in the graph
    rooted at (m,z)=(0,10q+4) with its exact source coefficient. -/
theorem bounded_l1_cone_in_shadow_graph
    (q u b d m : Nat)
    (hu : u+4*q+3=7*2^(16*q)) (hu1 : 1≤u)
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0) (hcost : m+2≤16*q) :
    ∃ (w z alpha : Nat),
      ShadowReach (16*q+9) (10*q+4) m z ∧
      0<z ∧ 4≤w ∧ (16*q+9)+m=w+z ∧
      2^m*(b+4*w)=alpha*2^(16*q) := by
  obtain ⟨_,_,hmass,henc⟩ := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  exact bounded_odd_cone_in_shadow_graph (16*q) (16*q+9)
    (6*u-2) (2*u+5) (6*q+5) (10*q+4) 42
    hmass (by omega) (by omega) (by omega) (by omega) henc
    b d m hcone hmod hcost

#print axioms bounded_l0_cone_in_shadow_graph
#print axioms bounded_l1_cone_in_shadow_graph
end BB6.Shadow
