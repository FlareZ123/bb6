import SourceBridge
namespace BB6.Agent8Reset
open BB6.Agent28

/-- Exact source-genuine affine-wall histories obey an unconditional
    exponential lower bound on the fixed-reset budget. -/
theorem source_wall_resets_need_exponential_budget
    (n b d m z : Nat) (hn:14≤n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall : b=4*(m+n)) :
    7*2^n ≤ budget (n+2) z*(3*budget (n+2) z+3*n+8) := by
  by_cases hbig : 7*2^n ≤ budget (n+2) z*(3*budget (n+2) z+3*n+8)
  · exact hbig
  · have hsmall : budget (n+2) z*(3*budget (n+2) z+3*n+8)<7*2^n := by omega
    exact False.elim (source_counted_no_wall_when_budget_small n b d m z hn hcone hwall hsmall)

#print axioms BB6.Agent8Reset.source_wall_resets_need_exponential_budget
end BB6.Agent8Reset
