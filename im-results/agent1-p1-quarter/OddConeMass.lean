import MassInverse
namespace BB6.Agent1Quarter
open BB6.Agent47P1

inductive OddCone (b0 d0 : Nat) : Nat → Nat → Nat → Prop where
  | root : OddCone b0 d0 b0 d0 0
  | parent (b d m t k c : Nat)
      (hcone : OddCone b0 d0 b d m)
      (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
      (hi : inverseAt b d t = some (k,c))
      (hk : 2≤k) (hc : c%2=1) :
      OddCone b0 d0 (2*k-4) (c+4) (m+t+1)

theorem odd_cone_mass (b0 d0 b d m : Nat)
    (h : OddCone b0 d0 b d m) :
    b+d+2*m=b0+d0 := by
  induction h with
  | root => omega
  | parent b d m t k c hcone hb hb4 hd hi hk hc ih =>
    have hm := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hc
    omega

theorem l0_odd_cone_mass (u b d m:Nat) (hu:1≤u)
    (h:OddCone (4*u-4) (4*u+9) b d m) :
    b+d+2*m=8*u+5 := by
  have hm := odd_cone_mass _ _ b d m h
  omega

theorem l1_odd_cone_mass (u b d m:Nat) (hu:1≤u)
    (h:OddCone (6*u-2) (2*u+5) b d m) :
    b+d+2*m=8*u+3 := by
  have hm := odd_cone_mass _ _ b d m h
  omega

#print axioms odd_cone_mass
#print axioms l0_odd_cone_mass
#print axioms l1_odd_cone_mass
end BB6.Agent1Quarter
