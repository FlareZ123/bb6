import SpaceNeedleClosed
import NeedleValHalf

namespace BB6.Agent20.SpaceNeedleVal
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- A universally strict upper bound for the two-adic valuation of every
valid immediate predecessor of an original high-level terminal tower. -/
theorem source_terminal_predecessor_valuation (q v k : Nat)
    (h : highLevelNext (.N (oddTower q v)) = some (.N (haltTower k))) :
    2*v < k+1 := by
  exact NeedleValHalf.source_equation_valuation_strict q v k
    ((predecessor_power_identity q v k).mp h)

#print axioms source_terminal_predecessor_valuation
end BB6.Agent20.SpaceNeedleVal
