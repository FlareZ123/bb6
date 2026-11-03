module
public import Agent18BOneDim

@[expose] public section
namespace BB6.BScaledGrowth
open OneDim

/-- Scalar Machine B is squeezed between two affine rays of slope 3/2. -/
theorem G_lower_step (z : Nat) : 3*(z+8) ≤ 2*(G z+8) := by
  simp only [G]
  omega

theorem G_upper_step (z : Nat) : 2*(G z+15) ≤ 3*(z+15) := by
  simp only [G]
  omega

/-- Exact lower bound, with the sharp exponential rate 3/2. -/
theorem iter_lower (n z : Nat) :
    3^n*(z+8) ≤ 2^n*(iterG n z+8) := by
  induction n generalizing z with
  | zero => simp [iterG]
  | succ n ih =>
    have hstep := G_lower_step z
    have a := Nat.mul_le_mul_left (3^n) hstep
    have b := Nat.mul_le_mul_left 2 (ih (G z))
    change 3^(n+1)*(z+8) ≤ 2^(n+1)*(iterG n (G z)+8)
    simp only [Nat.pow_succ]
    calc
      (3^n * 3) * (z+8) = 3^n * (3*(z+8)) := by ac_rfl
      _ ≤ 3^n * (2*(G z+8)) := a
      _ = 2 * (3^n*(G z+8)) := by ac_rfl
      _ ≤ 2 * (2^n*(iterG n (G z)+8)) := b
      _ = (2^n*2)*(iterG n (G z)+8) := by ac_rfl

/-- Exact upper bound, with the sharp exponential rate 3/2. -/
theorem iter_upper (n z : Nat) :
    2^n*(iterG n z+15) ≤ 3^n*(z+15) := by
  induction n generalizing z with
  | zero => simp [iterG]
  | succ n ih =>
    have hstep := G_upper_step z
    have a := Nat.mul_le_mul_left (3^n) hstep
    have b := Nat.mul_le_mul_left 2 (ih (G z))
    change 2^(n+1)*(iterG n (G z)+15) ≤ 3^(n+1)*(z+15)
    simp only [Nat.pow_succ]
    calc
      (2^n*2)*(iterG n (G z)+15) = 2 * (2^n*(iterG n (G z)+15)) := by ac_rfl
      _ ≤ 2 * (3^n*(G z+15)) := b
      _ = 3^n * (2*(G z+15)) := by ac_rfl
      _ ≤ 3^n * (3*(z+15)) := a
      _ = (3^n*3)*(z+15) := by ac_rfl

/-- A certified bit-size bracket for the blank scalar orbit. -/
theorem blank_sandwich (n : Nat) :
    8*3^n ≤ 2^n*(iterG n 0+8) ∧
    2^n*(iterG n 0+15) ≤ 15*3^n := by
  constructor
  · simpa only [Nat.zero_add, Nat.mul_comm] using iter_lower n 0
  · simpa only [Nat.zero_add, Nat.mul_comm] using iter_upper n 0

/-- Exact two-sided growth control of every synthetically continued Machine B reset. -/
theorem reset_sandwich (n : Nat) :
    8*3^(scalarA n) ≤ 2^(scalarA n)*(scalarA (n+1)+2) ∧
    2^(scalarA n)*(scalarA (n+1)+6) ≤ 15*3^(scalarA n) := by
  let z := iterG (scalarA n) 0
  have h := blank_sandwich (scalarA n)
  have hc : scalarA (n+1) = z+9-3*(z%2) := rfl
  have hp : z%2 ≤ 1 := by omega
  have hlow : z+8 ≤ scalarA (n+1)+2 := by omega
  have hupp : scalarA (n+1)+6 ≤ z+15 := by omega
  constructor
  · exact Nat.le_trans h.1 (Nat.mul_le_mul_left _ hlow)
  · exact Nat.le_trans (Nat.mul_le_mul_left _ hupp) h.2

#print axioms reset_sandwich

#print axioms blank_sandwich
#print axioms iter_lower
#print axioms iter_upper
end BB6.BScaledGrowth
