import ExceptionalBudgetSource
import BudgetGrowth
namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter

/-- Every genuine critical P1 exceptional c=1 (d=5) odd inverse history
with z positive-depth resets must satisfy an exponential-vs-polynomial
degree constraint. The degree is defined by e(0)=1, e(k+1)=4e(k)+1. -/
theorem source_exceptional_reset_degree_bound
    (n b d m z : Nat) (hn : 14≤n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hd : d=5) :
    2^n ≤ (20*(n+2))^(degreeBound z) := by
  have hLower := source_critical_d5_needs_exponential_reset_budget
    n b d m z hn hcone hd
  have hUpper := budget_upper_power z (n+2) (by omega)
  omega

#print axioms BB6.Agent8Reset.source_exceptional_reset_degree_bound
end BB6.Agent8Reset
