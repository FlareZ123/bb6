import UniformReachBounds
import GenericCriticalReachParamK

namespace BB6.Agent9UniformParamK
open BB6.Precision

/-- Any closed base predicate automatically bounds all genuine scalar paths
    for an arbitrary 2^(K+B) perturbation of one P1 feeder. -/
theorem lift_feeder_bounds (K B qbase side c : Nat)
    (S : Nat → Nat → Prop)
    (hroot : S 0 (c*qbase+4))
    (hsmall : ∀ m z, S m z → m≤B)
    (hnodiv : ∀ m z, S m z → ¬2^K∣z)
    (hclosed : ∀ m z t v zp, S m z → z=2^t*v →
        2*zp+1=16*qbase+side+m+t+v → S (m+t+1) zp)
    (r m z : Nat)
    (hpath : ShadowReach (16*(qbase+2^(K+B)*r)+side)
        (c*(qbase+2^(K+B)*r)+4) m z) :
    m≤B ∧ ¬2^K∣z := by
  have hL : 16*(qbase+2^(K+B)*r)+side =
      (16*qbase+side)+16*2^(K+B)*r := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hR : c*(qbase+2^(K+B)*r)+4 =
      (c*qbase+4)+2^(K+B)*(c*r) := by
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hpath' : ShadowReach ((16*qbase+side)+16*2^(K+B)*r)
      ((c*qbase+4)+2^(K+B)*(c*r)) m z := by
    simpa only [hL,hR] using hpath
  have hh := uniform_reach_bounds K B (16*qbase+side)
      (c*qbase+4) r c S hroot hsmall hnodiv hclosed m z hpath'
  exact hh

/-- UNIVERSAL ORIGINAL-SOURCE P1 gateway cylinder.
    Any authentic finite base shadow certificates of cost at most 41,
    avoiding 1024 divisibility, automatically exclude all parameter
    translates q=qbase+2^51*r. This constructs no parametric node list. -/
theorem universal_blank_critical_cylinder_param_K
    (K B qbase : Nat) (hqbase : 29≤qbase) (hB:B+K+3≤15*qbase)
    (nodes0 nodes1 : List (Nat×Nat))
    (hroot0 : (0,12*qbase+4)∈nodes0)
    (hroot1 : (0,10*qbase+4)∈nodes1)
    (hclosed0 : ∀ m z t v zp, (m,z)∈nodes0 →
        z=2^t*v → 2*zp+1=16*qbase+8+m+t+v →
        (m+t+1,zp)∈nodes0)
    (hclosed1 : ∀ m z t v zp, (m,z)∈nodes1 →
        z=2^t*v → 2*zp+1=16*qbase+9+m+t+v →
        (m+t+1,zp)∈nodes1)
    (hsmall0 : ∀ m z, (m,z)∈nodes0 → m≤B)
    (hsmall1 : ∀ m z, (m,z)∈nodes1 → m≤B)
    (hnodiv0 : ∀ m z, (m,z)∈nodes0 → ¬2^K∣z)
    (hnodiv1 : ∀ m z, (m,z)∈nodes1 → ¬2^K∣z)
    (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(qbase+2^(K+B)*r)+2) -
       2*(16*(qbase+2^(K+B)*r)+2)-10) := by
  let q := qbase+2^(K+B)*r
  have hq : 29≤q := by dsimp [q]; omega
  have hs0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → m≤B := by
    intro m z hp
    exact (lift_feeder_bounds K B qbase 8 12 (fun m z => (m,z)∈nodes0)
      hroot0 hsmall0 hnodiv0 hclosed0 r m z hp).1
  have hs1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → m≤B := by
    intro m z hp
    exact (lift_feeder_bounds K B qbase 9 10 (fun m z => (m,z)∈nodes1)
      hroot1 hsmall1 hnodiv1 hclosed1 r m z hp).1
  have hn0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → ¬2^K∣z := by
    intro m z hp
    exact (lift_feeder_bounds K B qbase 8 12 (fun m z => (m,z)∈nodes0)
      hroot0 hsmall0 hnodiv0 hclosed0 r m z hp).2
  have hn1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → ¬2^K∣z := by
    intro m z hp
    exact (lift_feeder_bounds K B qbase 9 10 (fun m z => (m,z)∈nodes1)
      hroot1 hsmall1 hnodiv1 hclosed1 r m z hp).2
  exact BB6.Agent9GenericReachParamK.critical_unreachable_of_reach_param_K
    K B q hq (by dsimp [q]; omega) hs0 hs1 hn0 hn1

#print axioms lift_feeder_bounds
#print axioms universal_blank_critical_cylinder_param_K
end BB6.Agent9UniformParamK
