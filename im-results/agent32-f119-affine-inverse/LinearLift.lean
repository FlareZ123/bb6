import Init

namespace AffineInverse

theorem pow_linear (g l j : Int) (h : g ∣ l) (k : Nat) :
    ∃ z : Int, (1+l*j)^k = 1+(k:Int)*l*j+(l*g)*z := by
  obtain ⟨q,hq⟩ := h
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨z*(1+l*j)+(k:Int)*q*j*j, ?_⟩
    rw [Int.pow_succ, hz, Int.natCast_succ]
    grind

theorem lift_iff (g l j A d : Int) (h : g ∣ l) (hl : l ≠ 0) (k : Nat) :
    l*g ∣ A*(1+l*j)^k - (A+l*d) ↔ g ∣ A*j*(k:Int)-d := by
  obtain ⟨z,hz⟩ := pow_linear g l j h k
  rw [hz]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v-A*z, ?_⟩
    have he : l*(A*j*(k:Int)-d) = l*(g*(v-A*z)) := by grind
    exact Int.eq_of_mul_eq_mul_left hl he
  · rintro ⟨v,hv⟩
    exact ⟨v+A*z, by grind⟩

#print axioms pow_linear
#print axioms lift_iff
end AffineInverse
