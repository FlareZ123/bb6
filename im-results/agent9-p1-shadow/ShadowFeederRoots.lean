import ShadowConeLift
namespace BB6.Shadow
open BB6.Agent1Quarter

/-- Exact arithmetic initialization of both original P1 critical feeder roots. -/
theorem two_feeder_root_arithmetic (q u P : Nat)
    (hu : u+4*q+3=7*P) (hu1 : 1≤u) :
    (4*u-4)+(4*u+9)+2*(16*q+8)+3=56*P ∧
    (4*u-4)+4*(4*q+4)=28*P ∧
    (6*u-2)+(2*u+5)+2*(16*q+9)+3=56*P ∧
    (6*u-2)+4*(6*q+5)=42*P := by omega

/-- Every bounded-cost authentic L0 feeder-cone hub admits the exact
    shadow coordinates used by the computational census. -/
theorem bounded_l0_cone_has_shadow
    (q u b d m : Nat)
    (hu : u+4*q+3=7*2^(16*q)) (hu1 : 1≤u)
    (hcone : OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0) (hcost : m+2≤16*q) :
    ∃ (w z alpha : Nat),
      0<z ∧ 4≤w ∧ (16*q+8)+m=w+z ∧
      2^m*(b+4*w)=alpha*2^(16*q) := by
  obtain ⟨hmass,henc,_,_⟩ := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  exact bounded_odd_cone_has_shadow (16*q) (16*q+8)
    (4*u-4) (4*u+9) (4*q+4) (12*q+4) 28
    hmass (by omega) (by omega) (by omega) (by omega) henc
    b d m hcone hmod hcost

/-- Every bounded-cost authentic L1 feeder-cone hub admits the exact
    shadow coordinates used by the computational census. -/
theorem bounded_l1_cone_has_shadow
    (q u b d m : Nat)
    (hu : u+4*q+3=7*2^(16*q)) (hu1 : 1≤u)
    (hcone : OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0) (hcost : m+2≤16*q) :
    ∃ (w z alpha : Nat),
      0<z ∧ 4≤w ∧ (16*q+9)+m=w+z ∧
      2^m*(b+4*w)=alpha*2^(16*q) := by
  obtain ⟨_,_,hmass,henc⟩ := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  exact bounded_odd_cone_has_shadow (16*q) (16*q+9)
    (6*u-2) (2*u+5) (6*q+5) (10*q+4) 42
    hmass (by omega) (by omega) (by omega) (by omega) henc
    b d m hcone hmod hcost

#print axioms two_feeder_root_arithmetic
#print axioms bounded_l0_cone_has_shadow
#print axioms bounded_l1_cone_has_shadow
end BB6.Shadow
