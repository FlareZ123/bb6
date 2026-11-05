import Q297Depth
import Q297Power
import ShadowNoExceptionalGeneral
import P1InverseLog
import OddConeMass

namespace BB6.Agent8Q297
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Shadow

/-- No exact exceptional c=1 source inverse can occur at an authentic L0 node. -/
theorem l0_all_r_no_exceptional
    (r u b d m t k : Nat)
    (hu : u+4*(297+1024*r)+3=7*2^(16*(297+1024*r)))
    (hu1 : 1≤u)
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0)
    (hi : inverseAt b d t=some (k,1)) : False := by
  let q := 297+1024*r
  have hcost := l0_all_r_authentic_cost r u b d m hu hu1 hcone hmod
  have hdpt := l0_all_r_inverse_depth r u b d m t k 1 hu hu1 hcone hmod hi
  have hmass0 := odd_cone_mass (4*u-4) (4*u+9) b d m hcone
  have hroot := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hmass : b+d+2*m+2*(16*q+8)+3=56*2^(16*q) := by omega
  have hbig := pow16_dominates_hub q m 8 (by omega) hcost (by omega)
  have hshift := shifted_gt_power (16*q) (16*q+8) m b d
     hmass (by exact hbig.1) (by omega)
  have hpow := inverseAt_power b d t k 1 hi
  have ht : 2^t≤2^8 := Nat.pow_le_pow_right (by decide) hdpt
  have hsmall : d+b/2+3≤1024 := by omega
  have hn : 1024<2^(16*q) := hbig.2
  omega

/-- No exact exceptional c=1 source inverse can occur at an authentic L1 node. -/
theorem l1_all_r_no_exceptional
    (r u b d m t k : Nat)
    (hu : u+4*(297+1024*r)+3=7*2^(16*(297+1024*r)))
    (hu1 : 1≤u)
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0)
    (hi : inverseAt b d t=some (k,1)) : False := by
  let q := 297+1024*r
  have hcost := l1_all_r_authentic_cost r u b d m hu hu1 hcone hmod
  have hdpt := l1_all_r_inverse_depth r u b d m t k 1 hu hu1 hcone hmod hi
  have hmass0 := odd_cone_mass (6*u-2) (2*u+5) b d m hcone
  have hroot := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hmass : b+d+2*m+2*(16*q+9)+3=56*2^(16*q) := by omega
  have hbig := pow16_dominates_hub q m 9 (by omega) hcost (by omega)
  have hshift := shifted_gt_power (16*q) (16*q+9) m b d
     hmass (by exact hbig.1) (by omega)
  have hpow := inverseAt_power b d t k 1 hi
  have ht : 2^t≤2^8 := Nat.pow_le_pow_right (by decide) hdpt
  have hsmall : d+b/2+3≤1024 := by omega
  have hn : 1024<2^(16*q) := hbig.2
  omega

#print axioms l0_all_r_no_exceptional
#print axioms l1_all_r_no_exceptional
end BB6.Agent8Q297
