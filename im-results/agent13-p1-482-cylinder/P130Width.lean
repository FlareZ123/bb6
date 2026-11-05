import P130Source
import P130Power
import ShortConeBridge

namespace BB6.Agent13P130
open BB6.Agent1Quarter BB6.Agent1ShortCone

/-- Uniform positive-left lower bound for authentic L0 cone nodes. -/
theorem l0_hub_large (r u b d m:Nat)
    (hu : u+4*(30+256*r)+3=7*2^(16*(30+256*r)))
    (hu1 : 1≤u)
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0) : 24≤b := by
  have hm := l0_all_r_authentic_cost r u b d m hu hu1 hcone hmod
  have hleft := odd_cone_left_bound (4*u-4) (4*u+9) b d m hcone
  have hpow : (2:Nat)^m≤2^10 := Nat.pow_le_pow_right (by decide) hm
  have hscaled : 2^m*(b+12)≤2^10*(b+12) :=
    Nat.mul_le_mul_right (b+12) hpow
  have hroot : (4*u-4)+12=4*u+8 := by omega
  have hwide := l0_root_wide r u hu
  by_cases hb : 24≤b
  · exact hb
  exfalso
  have hupper : b+12≤36 := by omega
  have hscaled2 : 2^10*(b+12)≤2^10*36 := Nat.mul_le_mul_left _ hupper
  omega

/-- Uniform positive-left lower bound for authentic L1 cone nodes. -/
theorem l1_hub_large (r u b d m:Nat)
    (hu : u+4*(30+256*r)+3=7*2^(16*(30+256*r)))
    (hu1 : 1≤u)
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0) : 24≤b := by
  have hm := l1_all_r_authentic_cost r u b d m hu hu1 hcone hmod
  have hleft := odd_cone_left_bound (6*u-2) (2*u+5) b d m hcone
  have hpow : (2:Nat)^m≤2^10 := Nat.pow_le_pow_right (by decide) hm
  have hscaled : 2^m*(b+12)≤2^10*(b+12) :=
    Nat.mul_le_mul_right (b+12) hpow
  have hroot : (6*u-2)+12=6*u+10 := by omega
  have hwide := l1_root_wide r u hu
  by_cases hb : 24≤b
  · exact hb
  exfalso
  have hupper : b+12≤36 := by omega
  have hscaled2 : 2^10*(b+12)≤2^10*36 := Nat.mul_le_mul_left _ hupper
  omega

#print axioms l0_hub_large
#print axioms l1_hub_large
end BB6.Agent13P130
