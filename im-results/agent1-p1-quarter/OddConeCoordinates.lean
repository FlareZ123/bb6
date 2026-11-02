import OddConeMass
namespace BB6.Agent1Quarter

theorem odd_cone_left_even (b0 d0 b d m : Nat)
    (hroot:b0%2=0) (h:OddCone b0 d0 b d m) : b%2=0 := by
  induction h with
  | root => exact hroot
  | parent b d m t k c hcone hb hb4 hd hi hk hc ih => omega

/-- Exact lossless 2D coordinate system: mass depth m and shifted-right
    s determine both counters in any positive-odd inverse cone. -/
theorem odd_cone_two_linear_coordinates (b0 d0 b d m : Nat)
    (hroot:b0%2=0) (h:OddCone b0 d0 b d m) :
    b+2*(d+b/2+3)+4*m=2*(b0+d0)+6 ∧
    d+(b0+d0)+6=2*(d+b/2+3)+2*m := by
  have heven:=odd_cone_left_even b0 d0 b d m hroot h
  have hmass:=odd_cone_mass b0 d0 b d m h
  omega

theorem l0_odd_cone_coordinates (u b d m:Nat) (hu:1≤u)
    (h:OddCone (4*u-4) (4*u+9) b d m) :
    b+2*(d+b/2+3)+4*m=16*u+16 := by
  have heq := (odd_cone_two_linear_coordinates (4*u-4) (4*u+9) b d m (by omega) h).1
  omega

theorem l1_odd_cone_coordinates (u b d m:Nat) (hu:1≤u)
    (h:OddCone (6*u-2) (2*u+5) b d m) :
    b+2*(d+b/2+3)+4*m=16*u+12 := by
  have heq := (odd_cone_two_linear_coordinates (6*u-2) (2*u+5) b d m (by omega) h).1
  omega

#print axioms odd_cone_two_linear_coordinates
#print axioms l0_odd_cone_coordinates
#print axioms l1_odd_cone_coordinates
end BB6.Agent1Quarter
