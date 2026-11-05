import CylinderDepth
import MediumConeReach

namespace BB6.Agent8Cylinder
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1ShortCone BB6.Agent45TwoRoot

/-- Every exact even-output inverse terminal violates the necessary
    fourteen-power shape of a blank-reachable P1 even input. -/
theorem l0_all_r_no_even_power
    (r u b d m t k c j : Nat)
    (hu : u+4*(29+1024*r)+3=7*2^(16*(29+1024*r)))
    (hu1 : 1≤u) (hu2 : u=u2 (29+1024*r))
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hb:8≤b)(hmod:b%4=0)(hd:d%2=1)
    (hi : inverseAt b d t=some (k,c)) (hc:c%2=0) :
    2*k+8≠14*2^j := by
  let q := 29+1024*r
  have hm := l0_all_r_authentic_cost r u b d m hu hu1 hcone hmod
  have ht := l0_all_r_inverse_depth r u b d m t k c hu hu1 hcone hmod hi
  have hcost : m+t+1≤15*q := by omega
  have hcone' : OddCone (4*u2 q-4) (4*u2 q+9) b d m := by
    simpa only [hu2] using hcone
  exact medium_root_even_not_power q b d m t k c j true
    (by omega) (by simpa using hcone') hb hmod hd hi hc hcost

/-- Every exact even-output inverse terminal violates the necessary
    fourteen-power shape of a blank-reachable P1 even input. -/
theorem l1_all_r_no_even_power
    (r u b d m t k c j : Nat)
    (hu : u+4*(29+1024*r)+3=7*2^(16*(29+1024*r)))
    (hu1 : 1≤u) (hu2 : u=u2 (29+1024*r))
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hb:8≤b)(hmod:b%4=0)(hd:d%2=1)
    (hi : inverseAt b d t=some (k,c)) (hc:c%2=0) :
    2*k+8≠14*2^j := by
  let q := 29+1024*r
  have hm := l1_all_r_authentic_cost r u b d m hu hu1 hcone hmod
  have ht := l1_all_r_inverse_depth r u b d m t k c hu hu1 hcone hmod hi
  have hcost : m+t+1≤15*q := by omega
  have hcone' : OddCone (6*u2 q-2) (2*u2 q+5) b d m := by
    simpa only [hu2] using hcone
  exact medium_root_even_not_power q b d m t k c j false
    (by omega) (by simpa using hcone') hb hmod hd hi hc hcost

#print axioms l0_all_r_no_even_power
#print axioms l1_all_r_no_even_power
end BB6.Agent8Cylinder
