import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20MixedValuation

/-- A 3-valuation predecessor cannot inherit a 5-valuation
    incoming edge when the target itself has such an edge. -/
theorem no_three_then_five (B P : Nat)
    (edge : 16 * B = 19 * P + 24)
    (target : 67 ∣ 3 * B + 224) :
    ¬ (67 ∣ 3 * P + 224) := by
  intro parent
  rcases target with ⟨x, hx⟩
  rcases parent with ⟨y, hy⟩
  omega

/-- The reverse order is likewise impossible. -/
theorem no_five_then_three (B P : Nat)
    (edge : 64 * B = 67 * P + 224)
    (target : 19 ∣ 3 * B + 24) :
    ¬ (19 ∣ 3 * P + 24) := by
  intro parent
  rcases target with ⟨x, hx⟩
  rcases parent with ⟨y, hy⟩
  omega

#print axioms no_three_then_five
#print axioms no_five_then_three
end BB6.Agent20MixedValuation
