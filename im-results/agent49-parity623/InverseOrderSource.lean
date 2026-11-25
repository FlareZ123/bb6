import InverseOrder
import DrainCorrectionGrowth

namespace BB6.Agent49InverseOrder
open BB6.Agent49CorrectionGrowth

theorem exactLaws : Laws excess drift := by
  refine ⟨excess_zero,excess_three,excess_one,excess_two,?_,?_,?_,?_⟩
  · rw [drift]; simp
  · intro q hq
    conv => lhs; rw [drift]
    simp [show 3*q≠0 by omega, show (3*q)%3=0 by omega, show (3*q)/3=q by omega]
  · intro q
    conv => lhs; rw [drift]
    simp [show 3*q+1≠0 by omega, show (3*q+1)%3=1 by omega, show (3*q+1)/3=q by omega]
  · intro q
    conv => lhs; rw [drift]
    simp [show 3*q+2≠0 by omega, show (3*q+2)%3=2 by omega, show (3*q+2)/3=q by omega]

theorem exact_gap (b : Nat) :
    (H excess drift (b+2)-H excess drift b = 4 ∨
     H excess drift (b+2)-H excess drift b = 8 ∨
     H excess drift (b+2)-H excess drift b = 10) := (adjacent exactLaws b).1

/-- The generic contraction instantiated on the exact source-linked
positive-budget statistics used by InverseWindowSource. -/
theorem exact_inverse_width (x x' : Int) (hx : x≤x') (b k : Nat) :
    x+G drift b ≤ x'+G drift (b+2*k) ∧
    x'+G drift (b+2*k)+(b+2*k : Nat) - (x+G drift b+b) +
      4*((k/3 : Nat) : Int) ≤ x'+F excess (b+2*k)-(x+F excess b) :=
  inverse_width exactLaws x x' hx b k

#print axioms exactLaws
#print axioms exact_gap
#print axioms exact_inverse_width
end BB6.Agent49InverseOrder
