import Q297Arithmetic
import ShadowFiniteInvariant
import ShadowFeederRoots

namespace BB6.Agent8Q297
open BB6.Agent1Quarter BB6.Shadow

/-- Authentic odd inverse hubs of the L0 feeder have bounded cumulative
cost throughout the infinite congruence q=297+1024r. -/
theorem l0_all_r_authentic_cost
    (r u b d m : Nat)
    (hu : u+4*(297+1024*r)+3=7*2^(16*(297+1024*r)))
    (hu1 : 1≤u)
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0) : m≤10 := by
  let q := 297+1024*r
  obtain ⟨hrootmass,henc,_,_⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hrootIn : (0,12*q+4) ∈ l0Nodes r := by
    simp [l0Nodes,q]
    omega
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    finite_shadow_invariant_lifts_full_cone
      (16*q) (16*q+8) (4*u-4) (4*u+9)
      (4*q+4) (12*q+4) 28 (l0Nodes r)
      hrootmass (by omega) (by omega)
      (by omega) (by omega) (by omega) henc
      hrootIn
      (fun m z t v zp hm hd hn => l0_closed r m z t v zp hm hd (by simpa [q] using hn))
      (fun m z hm => l0_small r m z hm)
      (fun m z hm => l0_no256 r m z hm)
      b d m hcone hmod
  exact l0_small r m z hmem

/-- Authentic odd inverse hubs of the L1 feeder satisfy the same cost bound. -/
theorem l1_all_r_authentic_cost
    (r u b d m : Nat)
    (hu : u+4*(297+1024*r)+3=7*2^(16*(297+1024*r)))
    (hu1 : 1≤u)
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0) : m≤10 := by
  let q := 297+1024*r
  obtain ⟨_,_,hrootmass,henc⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hrootIn : (0,10*q+4) ∈ l1Nodes r := by
    simp [l1Nodes,q]
    omega
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    finite_shadow_invariant_lifts_full_cone
      (16*q) (16*q+9) (6*u-2) (2*u+5)
      (6*q+5) (10*q+4) 42 (l1Nodes r)
      hrootmass (by omega) (by omega)
      (by omega) (by omega) (by omega) henc
      hrootIn
      (fun m z t v zp hm hd hn => l1_closed r m z t v zp hm hd (by simpa [q] using hn))
      (fun m z hm => l1_small r m z hm)
      (fun m z hm => l1_no256 r m z hm)
      b d m hcone hmod
  exact l1_small r m z hmem

#print axioms l0_all_r_authentic_cost
#print axioms l1_all_r_authentic_cost
end BB6.Agent8Q297
