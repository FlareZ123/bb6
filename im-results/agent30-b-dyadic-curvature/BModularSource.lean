import BModularCurvature
import Agent10BSource

namespace BB6.Agent30B

/-- All-iterate dyadic curvature transferred to Agent 18's Machine B scalar map. -/
theorem source_iterG_dyadic_curvature (n z : Nat) :
    (BB6.OneDim.iterG (n+1) z +
      BB6.OneDim.iterG (n+1) (z+2*2^n)+7 =
       2*BB6.OneDim.iterG (n+1) (z+2^n)) ∨
    (BB6.OneDim.iterG (n+1) z +
      BB6.OneDim.iterG (n+1) (z+2*2^n) =
       2*BB6.OneDim.iterG (n+1) (z+2^n)+7) := by
  simpa only [←BB6.Agent10B.iterG_eq_source] using
    iterG_dyadic_curvature n z

/-- No positive iterate of the actual scalar Machine B return map has
an all-input affine quotient modulo a number not dividing seven. -/
theorem source_affine_modulus_divides_seven (n m a b : Nat)
    (h : ∀ z, (BB6.OneDim.iterG (n+1) z)%m=(a*z+b)%m) :
    m ∣ 7 := by
  apply affine_iter_modulus_divides_seven n m a b
  intro z
  rw [BB6.Agent10B.iterG_eq_source]
  exact h z

#print axioms source_iterG_dyadic_curvature
#print axioms source_affine_modulus_divides_seven
end BB6.Agent30B
