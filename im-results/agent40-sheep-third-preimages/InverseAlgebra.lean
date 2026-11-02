import Std

/-!
# Reusable algebraic inverse criterion for the Sheep generic return branch

Write an odd tape-section parameter as u=2v+1. In the generic non-halting
branch v>=2. These equalities are exact for all natural a,v; the exceptional
case v=1 is handled separately by the actual machine acceleration.
-/

namespace SheepInverseAlgebra

def genericOdd (a v : Nat) : Nat := 2^a*(2*v+1)+a+v

/-- Eliminates odd-part division from the inverse problem. -/
theorem genericTwice (a v : Nat) :
    2*genericOdd a v+1=(2^(a+1)+1)*(2*v+1)+2*a := by
  unfold genericOdd
  simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Exact target equality iff a linear exponential Diophantine equation. -/
theorem preimage_iff (a v y : Nat) :
  genericOdd a v=y ↔ (2^(a+1)+1)*(2*v+1)+2*a=2*y+1 := by
  constructor
  · intro eq
    rw [← genericTwice, eq]
  · intro eq
    rw [← genericTwice] at eq
    omega

/-- Every generic predecessor satisfies this necessary modular condition. -/
theorem preimage_divisible (a v y : Nat) (h : genericOdd a v=y) :
    (2*y+1-2*a) % (2^(a+1)+1) = 0 := by
  have hh := (preimage_iff a v y).mp h
  have hcancel : 2*y+1-2*a=(2^(a+1)+1)*(2*v+1) := by omega
  rw [hcancel]
  simp

#print axioms genericTwice
#print axioms preimage_iff
#print axioms preimage_divisible
end SheepInverseAlgebra
