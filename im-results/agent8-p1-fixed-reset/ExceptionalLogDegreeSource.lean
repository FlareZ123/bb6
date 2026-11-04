import ExceptionalGrowthSource
import DegreeLogPure

namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter

/-- A genuine exceptional P1 c=1 feeder has an all-parameter
logarithmic lower bound on the inverse reset polynomial degree.
This is necessary for source-defined critical odd histories. -/
theorem source_exceptional_log_degree_bound
    (n b d m z : Nat) (hn : 14≤n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hd : d=5) :
    n < (Nat.log2 (20*(n+2))+1)*degreeBound z := by
  have hdegreePos : 0 < degreeBound z := by
    induction z with
    | zero => decide
    | succ z ih =>
        change 0 < 4*degreeBound z+1
        omega
  have hpower := source_exceptional_reset_degree_bound
    n b d m z hn hcone hd
  exact BB6.Agent8Log.power_log_degree_bound
    n (20*(n+2)) (degreeBound z) hdegreePos hpower

#print axioms BB6.Agent8Reset.source_exceptional_log_degree_bound
end BB6.Agent8Reset
