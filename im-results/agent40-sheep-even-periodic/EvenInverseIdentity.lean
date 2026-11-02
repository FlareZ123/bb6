import Std
namespace SheepEvenInverse

/-- Generic even-return inverse arithmetic; X=2^h, Y=3^h, A=2^a,
P=2^(j+s), d is the denominator, and b a signed affine offset. -/
theorem generic_inverse_identity
    (d X Y A U V a P : Nat) (b : Int)
    (hy : (d : Int) * (1 + (Y : Int)*(U : Int)) = (P : Int) + b)
    (hz : 2*(1 + (X : Int)*(U : Int)) =
      (2*(A : Int)+1)*(V : Int)+2*(a : Int)-1) :
    2*(X : Int)*(P : Int)
      + 2*((X : Int)*(b-(d : Int))+(d : Int)*(Y : Int))
      - (d : Int)*(Y : Int)*(2*(a : Int)-1)
      = ((d : Int)*(Y : Int))*(2*(A : Int)+1)*(V : Int) := by
  have hpoly :
      (2*(X : Int)*(P : Int)
      + 2*((X : Int)*(b-(d : Int))+(d : Int)*(Y : Int))
      - (d : Int)*(Y : Int)*(2*(a : Int)-1)) -
      ((d : Int)*(Y : Int))*(2*(A : Int)+1)*(V : Int) =
        (d : Int)*(Y : Int)*(2*(1+(X : Int)*(U : Int)) -
          ((2*(A : Int)+1)*(V : Int)+2*(a : Int)-1)) -
        2*(X : Int)*((d : Int)*(1+(Y : Int)*(U : Int))-((P : Int)+b)) := by
    simp [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hzero :
      (d : Int)*(Y : Int)*(2*(1+(X : Int)*(U : Int)) -
          ((2*(A : Int)+1)*(V : Int)+2*(a : Int)-1)) -
        2*(X : Int)*((d : Int)*(1+(Y : Int)*(U : Int))-((P : Int)+b)) = 0 := by
    rw [hy, hz]
    simp
  omega

/-- A necessary divisibility test for the odd-block inverse stage. -/
theorem high_h_divisibility
    (d Y U P : Nat) (b : Int)
    (hy : (d : Int)*(1+(Y : Int)*(U : Int))=(P : Int)+b) :
    ((P : Int)+b-(d : Int)) % ((d : Int)*(Y : Int)) = 0 := by
  have h : ((P : Int)+b-(d : Int)) = ((d : Int)*(Y : Int))*(U : Int) := by
    calc
      ((P : Int)+b-(d : Int)) = (d : Int)*(1+(Y : Int)*(U : Int))-(d : Int) := by rw [hy]
      _ = ((d : Int)*(Y : Int))*(U : Int) := by
        simp only [Int.mul_add, Int.mul_assoc]
        omega
  rw [h]
  exact Int.mul_emod_right _ _

/-- A necessary parity-correct congruence for every generic inverse. -/
theorem generic_inverse_parity
    (d X Y A U V a P : Nat) (b : Int)
    (hd : 0 < d) (hY : 0 < Y) (hv : V % 2 = 1)
    (hy : (d : Int) * (1 + (Y : Int)*(U : Int)) = (P : Int) + b)
    (hz : 2*(1 + (X : Int)*(U : Int)) =
      (2*(A : Int)+1)*(V : Int)+2*(a : Int)-1) :
    (2*(X : Int)*(P : Int)
      + 2*((X : Int)*(b-(d : Int))+(d : Int)*(Y : Int))
      - (d : Int)*(Y : Int)*(2*(a : Int)-1)) %
        ((2*d*Y*(2*A+1) : Nat) : Int) =
      (((d*Y*(2*A+1) : Nat) : Int)) := by
  have hidentity := generic_inverse_identity d X Y A U V a P b hy hz
  have hTpos : 0 < d*Y*(2*A+1) := Nat.mul_pos (Nat.mul_pos hd hY) (by omega)
  have hmod : ((d*Y*(2*A+1)*V : Nat) % (2*(d*Y*(2*A+1)))) =
     d*Y*(2*A+1) := by
    rw [show 2*(d*Y*(2*A+1)) = (d*Y*(2*A+1))*2 by omega]
    rw [Nat.mul_mod_mul_left, hv]
    omega
  have hmod2 : (d*Y*(2*A+1)*V) % (2*d*Y*(2*A+1)) = d*Y*(2*A+1) := by
    simpa only [Nat.mul_assoc] using hmod
  rw [hidentity]
  exact_mod_cast hmod2

#print axioms generic_inverse_identity
#print axioms high_h_divisibility
#print axioms generic_inverse_parity
end SheepEvenInverse
