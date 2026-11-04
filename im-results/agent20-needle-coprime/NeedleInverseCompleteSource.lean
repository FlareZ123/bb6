import SpaceNeedleClosed
import NeedleInverseComplete

namespace BB6.Agent20.SpaceNeedleInverse
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- An exact, executable and finite list of every genuine one-step incoming
source parameter pair to an original Space Needle high-level terminal. -/
theorem original_terminal_predecessors_iff_list (q v k : Nat) :
    (v,q) ∈ NeedleInverse.allTerminalPredecessors (k+1) ↔
      highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) := by
  rw [NeedleInverse.allTerminalPredecessors_spec]
  rw [NeedleInverse.original_source_equation_iff]
  exact (predecessor_power_identity q v k).symm

/-- The exact original source has at most half the terminal exponent's
immediate predecessors. -/
theorem original_terminal_fanin_bound (k : Nat) :
    (NeedleInverse.allTerminalPredecessors (k+1)).length ≤ (k+2)/2 := by
  exact NeedleInverse.at_most_half_fanin (k+1)

#print axioms original_terminal_predecessors_iff_list
#print axioms original_terminal_fanin_bound
end BB6.Agent20.SpaceNeedleInverse
