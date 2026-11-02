import Std

namespace SheepExceptional

/-- Strict binary-over-affine growth persists uniformly in a Nat exponent.
The nonnegative leading coefficient matters: the same statement is false
when A is allowed to be negative. Signed additive offsets are supported. -/
theorem binary_dominates_linear (A B C : Int) (J : Nat)
    (hA : 0 ≤ A)
    (hbase : B * (J:Int) + C < A * 2^J)
    (hslope : B ≤ A * 2^J) :
    ∀ n : Nat,
      B * ((J+n):Int) + C < A * 2^(J+n) ∧
      B ≤ A * 2^(J+n) := by
  intro n
  induction n with
  | zero =>
      simpa using And.intro hbase hslope
  | succ n ih =>
      obtain ⟨hleft,hright⟩ := ih
      have hp : (2:Int)^(J+(n+1)) = 2*2^(J+n) := by
        rw [show J+(n+1)=(J+n)+1 by omega, Int.pow_succ]
        ac_rfl
      have hlin : B * ((J+(n+1)):Int) + C =
          (B * ((J+n):Int)+C)+B := by
        push_cast
        simp only [Int.mul_add,Int.mul_one]
        omega
      push_cast
      rw [hlin,hp]
      have hm : A * (2*2^(J+n)) = 2 * (A*2^(J+n)) := by ac_rfl
      rw [hm]
      have hpown : 0≤(2:Int)^(J+n) := by
        have hh : 0<(2:Int)^(J+n) := Int.pow_pos (by decide)
        omega
      have hnonneg : 0≤A*2^(J+n) := Int.mul_nonneg hA hpown
      clear hlin hp hm hbase hslope
      constructor <;> omega

#print axioms binary_dominates_linear
end SheepExceptional
