import BudgetCoverage
import Margin34
import MarginSource

namespace BB6.Agent28ModScreen
open BB6.Agent28CarryBudget BB6.Agent43CarryCert BB6.Agent43MarginSource

/-- Finite critical-reset gate exclusion, not a whole-machine halting theorem. -/
theorem critical_reset_no_reach_budget_screen (n : Nat)
    (hn : 14≤n) (hhi : n≤10000) (he : n%2=0) (hs : survivor n=false) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  by_cases h34 : n=34
  · subst n
    exact critical_reset_no_reach_of_margin 34 30 (by decide) (by decide) margin34
  · obtain ⟨r,k,t,hr,hkn,hN,hempty,hbudget⟩ := certificate_with_budget n hn hhi he hs h34
    have hp := BB6WallCarry.pow2_ge_1100_mul n hn
    exact critical_reset_no_reach_of_margin n (k+1) hn he
      (margin_of_modular_certificate n r k t (by omega) hkn hN hr
        (budget_sound n k (by omega) hbudget) hempty)

#print axioms critical_reset_no_reach_budget_screen
end BB6.Agent28ModScreen
