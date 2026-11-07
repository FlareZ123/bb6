import PeriodPrimitive
import PeriodFiniteWord
namespace PeriodPrimitiveFinite

/-- Exact bound on the number of repetitions of *any* primitive mixed-depth
    word. No cost, depth, or period-size cutoff occurs. -/
theorem primitive_finite_bound (L : Nat) (w : List Nat) (N : Nat)
    (hp : ∃ t ∈ w, 0<t) (hprim : PeriodPrimitive.Primitive w)
    (m z : Nat → Nat)
    (hr : ∀ n<N+1, PeriodWord.Run L w (m n) (z n)
      (m (n+1)) (z (n+1))) :
    (2:Nat)^(PeriodWord.cost w * N) ≤
      (PeriodFinite.error (2^(PeriodWord.cost w))
        (PeriodWord.weight w:Int) (PeriodWord.cost w:Int)
        (fun n => (z n:Int)) 0).natAbs := by
  apply PeriodFiniteWord.finite_word_bound L w N
    (by have hh := PeriodPrimitive.positive_depth_cost w hp; omega) m z hr
  intro d hd
  exact PeriodPrimitive.primitive_no_integral_slope w hp hprim d hd

#print axioms primitive_finite_bound
end PeriodPrimitiveFinite
