import Std

namespace SheepEdgeIdentities

/-- Exact original-source generic inverse equation at d=1,c=0,h=3,a=6. -/
theorem root_h3_a6_to_Z (j x v : Nat)
    (hx : x = 2^6*v)
    (hs : (1*3^3)*(2^(6+1)+1)*v + 2*6*(1*3^3) + 2^(3+1)*1 + 2^(3+1)*0 =
      2^(j+3+1) + 3*(1*3^3)) :
    3483*x+16576=2^(j+10) := by
  have he : j+3+1=j+4 := by omega
  rw [he] at hs
  have hsource : 3483*v+259=2^(j+4) := by
    simp only [show (3:Nat)^3=27 by decide,
      show (2:Nat)^(6+1)=128 by decide,
      show (2:Nat)^(3+1)=16 by decide] at hs
    omega
  have hp : 2^(j+10)=64*2^(j+4) := by
    rw [show j+10=(j+4)+6 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hp,hx]
  omega

/-- The original generic (h=4,a=2) root branch has W as source. -/
theorem root_h4_a2_to_W (j x v : Nat)
    (hx : x = 2^2*v)
    (hs : (1*3^4)*(2^(2+1)+1)*v + 2*2*(1*3^4) + 2^(4+1)*1 + 2^(4+1)*0 =
      2^(j+4+1) + 3*(1*3^4)) :
    729*x+452=2^(j+7) := by
  have he : j+4+1=j+5 := by omega
  rw [he] at hs
  have hsource : 729*v+113=2^(j+5) := by
    simp only [show (3:Nat)^4=81 by decide,
      show (2:Nat)^(2+1)=8 by decide,
      show (2:Nat)^(4+1)=32 by decide] at hs
    omega
  have hp : 2^(j+7)=4*2^(j+5) := by
    rw [show j+7=(j+5)+2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hp,hx]
  omega

/-- The original generic (h=5,a=2) root branch has X as source. -/
theorem root_h5_a2_to_X (j x v : Nat)
    (hx : x = 2^2*v)
    (hs : (1*3^5)*(2^(2+1)+1)*v + 2*2*(1*3^5) + 2^(5+1)*1 + 2^(5+1)*0 =
      2^(j+5+1) + 3*(1*3^5)) :
    2187*x+1228=2^(j+8) := by
  have he : j+5+1=j+6 := by omega
  rw [he] at hs
  have hsource : 2187*v+307=2^(j+6) := by
    simp only [show (3:Nat)^5=243 by decide,
      show (2:Nat)^(2+1)=8 by decide,
      show (2:Nat)^(5+1)=64 by decide] at hs
    omega
  have hp : 2^(j+8)=4*2^(j+6) := by
    rw [show j+8=(j+6)+2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hp,hx]
  omega

/-- The original generic (h=0,a=2) edge into Z has T as source. -/
theorem Z_h0_a2_to_T (j x v : Nat)
    (hx : x = 2^2*v)
    (hs : (3483*3^0)*(2^(2+1)+1)*v + 2*2*(3483*3^0) +
      2^(0+1)*3483 + 2^(0+1)*16576 =
      2^((j+10)+0+1) + 3*(3483*3^0)) :
    31347*x+174404=2^(j+13) := by
  have he : j+10+0+1=j+11 := by omega
  rw [he] at hs
  have hsource : 31347*v+43601=2^(j+11) := by
    simp only [show (3:Nat)^0=1 by decide,
      show (2:Nat)^(2+1)=8 by decide,
      show (2:Nat)^(0+1)=2 by decide] at hs
    omega
  have hp : 2^(j+13)=4*2^(j+11) := by
    rw [show j+13=(j+11)+2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hp,hx]
  omega

#print axioms root_h3_a6_to_Z
#print axioms root_h4_a2_to_W
#print axioms root_h5_a2_to_X
#print axioms Z_h0_a2_to_T

end SheepEdgeIdentities
