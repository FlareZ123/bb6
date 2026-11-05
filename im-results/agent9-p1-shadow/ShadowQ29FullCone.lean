import ShadowFiniteInvariant
import ShadowQ29Graph
import ShadowQ29No256

namespace BB6.Shadow
open BB6.Agent1Quarter

private theorem q29L0_small (m z : Nat)
    (h : (m,z) ∈ q29L0Nodes) : m≤10 := by
  simp only [q29L0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

private theorem q29L1_small (m z : Nat)
    (h : (m,z) ∈ q29L1Nodes) : m≤10 := by
  simp only [q29L1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h
  omega

/-- All authentic q29 L0 odd inverse-cone hubs with left coordinate
    divisible by four have cost ≤10, unconditionally. -/
theorem q29_l0_full_authentic_cost
    (u b d m : Nat)
    (hu : u+4*29+3=7*2^(16*29))
    (hu1 : 1≤u)
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0) : m≤10 := by
  obtain ⟨hrootmass,henc,_,_⟩ :=
    two_feeder_root_arithmetic 29 u (2^(16*29)) hu hu1
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    finite_shadow_invariant_lifts_full_cone
      (16*29) (16*29+8) (4*u-4) (4*u+9)
      (4*29+4) (12*29+4) 28 q29L0Nodes
      hrootmass (by omega) (by omega)
      (by decide) (by decide) (by decide) henc
      (by decide)
      (fun m z t r zp hm hd hn => q29L0_closed m z t r zp hm hd hn)
      q29L0_small q29L0_no_256
      b d m hcone hmod
  exact q29L0_small m z hmem

/-- All authentic q29 L1 odd inverse-cone hubs with left coordinate
    divisible by four have cost ≤10, unconditionally. -/
theorem q29_l1_full_authentic_cost
    (u b d m : Nat)
    (hu : u+4*29+3=7*2^(16*29))
    (hu1 : 1≤u)
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0) : m≤10 := by
  obtain ⟨_,_,hrootmass,henc⟩ :=
    two_feeder_root_arithmetic 29 u (2^(16*29)) hu hu1
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    finite_shadow_invariant_lifts_full_cone
      (16*29) (16*29+9) (6*u-2) (2*u+5)
      (6*29+5) (10*29+4) 42 q29L1Nodes
      hrootmass (by omega) (by omega)
      (by decide) (by decide) (by decide) henc
      (by decide)
      (fun m z t r zp hm hd hn => q29L1_closed m z t r zp hm hd hn)
      q29L1_small q29L1_no_256
      b d m hcone hmod
  exact q29L1_small m z hmem

#print axioms q29_l0_full_authentic_cost
#print axioms q29_l1_full_authentic_cost
end BB6.Shadow
