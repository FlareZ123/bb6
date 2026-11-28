import FiniteCoefficientCone
import TypedCostBounds

namespace PeriodicMacro

/-- The affine slope forced by a nonempty positive-j word containing j>1 is
    a positive integer in the strict cone 3d<T. -/
theorem affine_equation_strict_slope
    (x : Letter) (xs : List Letter) (u0 u1 : Nat)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j)
    (heq : ((M (x::xs):Int)-1)*((u1:Int)-(u0:Int)) =
      ((A (x::xs)*T (x::xs)):Int)) :
    u0<u1 ∧ 3*(u1-u0)<T (x::xs) := by
  have hcone := coefficient_strict_cone (x::xs) hj hlarge
  have hT := typed_cost_lower x xs hj
  have hA : 0<A (x::xs) := by
    simp only [A]
    omega
  have hM : 1<M (x::xs) := by omega
  have hR : 0<A (x::xs)*T (x::xs) := Nat.mul_pos hA (by omega)
  have hdiff : 0<(u1:Int)-(u0:Int) := by
    by_cases hle : u1≤u0
    · have hdnon : (u1:Int)-(u0:Int)≤0 := by omega
      have hfac : 0≤(M (x::xs):Int)-1 := by omega
      have hprod : ((M (x::xs):Int)-1)*((u1:Int)-(u0:Int))≤0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos hfac hdnon
      have hcast : 0<((A (x::xs)*T (x::xs)):Int) := by exact_mod_cast hR
      rw [heq] at hprod
      omega
    · omega
  have hu : u0<u1 := by omega
  let d := u1-u0
  have hdcast : (d:Int)=(u1:Int)-(u0:Int) := by
    dsimp [d]
    omega
  have heqNat : (M (x::xs)-1)*d=A (x::xs)*T (x::xs) := by
    have hcast : (((M (x::xs)-1)*d : Nat):Int) =
        ((A (x::xs)*T (x::xs):Nat):Int) := by
      rw [Int.natCast_mul, Int.natCast_sub (by omega : 1≤M (x::xs))]
      simp only [Int.natCast_one]
      rw [hdcast]
      simpa only [Int.natCast_mul] using heq
    exact_mod_cast hcast
  have hcoef : 3*A (x::xs)<M (x::xs)-1 := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hcoef (by omega : 0<T (x::xs))
  have hleft : (M (x::xs)-1)*(3*d) = 3*(A (x::xs)*T (x::xs)) := by
    calc
      (M (x::xs)-1)*(3*d) = 3*((M (x::xs)-1)*d) := by ac_rfl
      _ = 3*(A (x::xs)*T (x::xs)) := by rw [heqNat]
  have hfactor : 0<M (x::xs)-1 := by omega
  have hslope : 3*d<T (x::xs) := by
    apply (Nat.mul_lt_mul_left hfactor).mp
    rw [hleft]
    have hm2 : 3*(A (x::xs)*T (x::xs)) <
        (M (x::xs)-1)*T (x::xs) := by
      calc
        3*(A (x::xs)*T (x::xs)) = (3*A (x::xs))*T (x::xs) := by ac_rfl
        _ < (M (x::xs)-1)*T (x::xs) := hmul
    exact hm2
  exact ⟨hu, by simpa [d] using hslope⟩

#print axioms affine_equation_strict_slope
end PeriodicMacro
