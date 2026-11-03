import Std
namespace BB6.Agent17Forward

private theorem cube_shift (z : Nat) :
    (z+1)^3 = 1 + z * ((z+1)*(z+1)+(z+1)+1) := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one,
             Nat.add_mul, Nat.mul_add, Nat.one_mul]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem div_three_factor (y : Nat) :
    ((3*y+1)*(3*y+1)+(3*y+1)+1) = 3*(1+3*y+y*(3*y)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem cube_three (y : Nat) :
    (1+3*y)^3 = 1+9*y*(1+3*y+y*(3*y)) := by
  have hs:=cube_shift (3*y)
  have hfactor:=div_three_factor y
  have hc : 3*y+1=1+3*y := by omega
  rw [hc] at hs
  rw [hc] at hfactor
  rw [hfactor] at hs
  have hh : 9*y*(1+3*y+y*(3*y)) =
      (3*y)*(3*(1+3*y+y*(3*y))) := by
    have hn : 9=3*3 := rfl
    rw [hn]
    ac_rfl
  rwa [hh]

private theorem cube_lift (k q : Nat) :
    (1+3^(k+1)*q)^3 =
    1+3^(k+2)*(q*(1+3*(3^k*q)+(3^k*q)*(3*(3^k*q)))) := by
  have h1 : 3^(k+1) = 3*3^k := by rw [Nat.pow_succ]; omega
  have h2 : 3^(k+2) = 9*3^k := by
    have h : k+2=k+1+1 := by omega
    rw [h,Nat.pow_succ,Nat.pow_succ]
    omega
  rw [h1,h2]
  have he : 1+(3*3^k)*q = 1+3*(3^k*q) := by ac_rfl
  rw [he]
  rw [cube_three (3^k*q)]
  congr 1
  ac_rfl

-- Recompiled, attributed transcription of Agent39's cubic lifting.
def Q : Nat → Nat
  | 0 => 1
  | k+1 =>
    Q k * (1 + 3*(3^k*Q k) + (3^k*Q k)*(3*(3^k*Q k)))

theorem power_three_lifting (k : Nat) :
    4^(3^k) = 1 + 3^(k+1)*Q k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : (3:Nat)^(k+1) = (3^k)*3 := by rw [Nat.pow_succ]
    calc
      4^(3^(k+1)) = (4^(3^k))^3 := by rw [hp,Nat.pow_mul]
      _ = (1+3^(k+1)*Q k)^3 := by rw [ih]
      _ = 1+3^(k+2)*(Q k*(1+3*(3^k*Q k)+(3^k*Q k)*(3*(3^k*Q k)))) := cube_lift k (Q k)
      _ = 1+3^((k+1)+1)*Q (k+1) := by rfl

#print axioms power_three_lifting
end BB6.Agent17Forward
