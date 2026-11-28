import PeriodicMacroTransfer

/-!
The exact transfer coefficient cone for positive exponent signed E/S pair words.
Paper strict extension when some exponent exceeds one is separate.
-/
namespace PeriodicMacro

theorem coefficient_weak_cone (xs : List Letter)
    (hj : ∀ x : Letter, x∈xs → 0<x.j) :
    3*A xs+1 ≤ M xs := by
  induction xs with
  | nil => simp [A,M]
  | cons x xs ih =>
    have hx : 0<x.j := hj x (by simp)
    have htail : ∀ y : Letter, y∈xs → 0<y.j := by
      intro y hy
      exact hj y (by simp [hy])
    have ht := ih htail
    have hs : 4≤scale x := scale_ge_four x hx
    have hm := Nat.mul_le_mul_left (scale x) ht
    simp only [A,M]
    have heq : 3*(1+scale x*A xs)+1 =
        4+scale x*(3*A xs) := by grind
    rw [heq]
    have hr : 4+scale x*(3*A xs) ≤
        scale x*(3*A xs+1) := by
      have hd : scale x*(3*A xs+1) =
          scale x*(3*A xs)+scale x := by grind
      rw [hd]
      omega
    exact le_trans hr hm

#print axioms coefficient_weak_cone
end PeriodicMacro
