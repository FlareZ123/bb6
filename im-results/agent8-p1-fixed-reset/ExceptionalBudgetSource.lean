import CostBudgetSource
import ExceptionalStrongSource

namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter

/-- Erase the exact number of positive-depth resets from an authentic
CountCone proof, preserving the original source inverse history. -/
theorem counted_is_odd
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) :
    OddCone b0 d0 b d m := by
  induction h with
  | root => exact OddCone.root
  | parent b d m z t k c hprev hb hb4 hd hi hk hc ih =>
      exact OddCone.parent b d m t k c ih hb hb4 hd hi hk hc

/-- A critical source inverse history reaching the exceptional c=1
feeder (encoded by d=5) must have a dyadic reset budget at least 2^n.
No upper bound on history length or reset count is assumed. -/
theorem source_critical_d5_needs_exponential_reset_budget
    (n b d m z : Nat) (hn : 14 ≤ n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hd : d=5) :
    2^n ≤ budget (n+2) z := by
  by_cases hneed : 2^n ≤ budget (n+2) z
  · exact hneed
  · have hsmall : budget (n+2) z < 2^n := by omega
    have hbound := source_counted_cost_lt_exponent n b d m z hn hcone hsmall
    have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
      counted_is_odd _ _ _ _ _ _ hcone
    have hcost := BB6.Agent8Exceptional.source_critical_odd_d5_needs_n_plus_four
      n b d m hn hodd hd
    omega

#print axioms BB6.Agent8Reset.source_critical_d5_needs_exponential_reset_budget
end BB6.Agent8Reset
