import ZeroEvenCostSource
import ExceptionalBudgetSource

namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent47P1

/-- A source-exact critical P1 c=0 exit compatible with original
blank reachability forces an exponentially large positive-depth
reset budget, for every reset count z. -/
theorem source_critical_zero_even_needs_exponential_reset_budget
    (n b d m z t k : Nat) (hn : 14≤n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hb : 8≤b) (hb4 : b%4=0)
    (hinv : inverseAt b d t = some (k,0)) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) 4) :
    2^n ≤ budget (n+2) z := by
  by_cases hneed : 2^n ≤ budget (n+2) z
  · exact hneed
  · have hsmall : budget (n+2) z < 2^n := by omega
    have hcost : m<n :=
      source_counted_cost_lt_exponent n b d m z hn hcone hsmall
    have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
      counted_is_odd _ _ _ _ _ _ hcone
    have hzero := BB6.Agent8Zero.source_critical_zero_even_exit_large_cost
      n b d m t k hn hodd hb hb4 hinv hk hreach
    have hdom := BB6.Agent8Zero.n_plus_four_le_pow n (by omega)
    omega

#print axioms BB6.Agent8Reset.source_critical_zero_even_needs_exponential_reset_budget
end BB6.Agent8Reset
