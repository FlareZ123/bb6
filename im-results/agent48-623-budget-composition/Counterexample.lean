import Agent8RootCancellationBudgetInterfaces
import Agent49TerminalRatio4Source
import Lean.Elab.Tactic.Omega

/-!
# Exact synthetic counterexample to three-step safety from the cancellation budget

This is an intermediate source-level diagnostic, not a blank-root reachability
claim.  It gives an exact three-transition halting chain whose predecessor
satisfies the far/far cancellation adapter's hypotheses and resulting
logOuterBudget.  Thus the existing two-step safety predicate on that
predecessor cannot be upgraded to three-step survival from the budget alone.

The states are
  D(260178,20001) -> D(240172,60031) -> D(180132,180131) -> halt.
The middle state is in the odd far-left terminal ratio-four window; the
first state is in logOuterBudget at exponent 16 and in the n=10 root band.
-/

namespace BB6.Agent48TerminalBudgetCounterexample

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent8RootCancellationBudgetInterfaces
open BB6.Agent8LogParentSource
open BB6.Agent49TerminalRatio4Source

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The predecessor scale lies in the canonical n=10 band. -/
theorem predecessor_root_band :
    10 <= 10 /\
    3^(10-1)-3 <= min 260178 20001 /\
    min 260178 20001 + 3 < 3^10 := by
  decide

/-- The source terminal-ratio theorem applies to the middle state and its
halting child, using depth 14 and mass exponent 16. -/
theorem middle_terminal_ratio4_window :
    4*60031 <= 240172+16+5*14+29 /\
    240172 <= 4*60031+16+5*14+29 := by
  exact oddFar_terminal_ratio4_source
    240172 60031 14 16 180132 180131 1 5
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- The actual transition q -> p is the odd far-left source branch. -/
theorem predecessor_to_middle :
    highLevelNext (.D 260178 20001) = some (.D 240172 60031) := by
  decide

/-- The actual transition p -> h is the odd far-left source branch. -/
theorem middle_to_terminal :
    highLevelNext (.D 240172 60031) = some (.D 180132 180131) := by
  decide

/-- The third state is genuinely terminal under the original accelerated
transition, despite the two successful preceding transitions. -/
theorem terminal_halts :
    highLevelNext (.D 180132 180131) = none := by
  decide

/-- The terminal parent has the required odd far-left source geometry. -/
theorem middle_branch_geometry :
    60031+5 <= 240172 /\
    60031+3 < 3^14 /\
    180132%2=0 /\
    2*(240172+2*60031+10+3*14)+5 < 3^16 := by
  decide

/-- The terminal ratio window fits the cancellation bridge's coarser
B=9*n+55 bound. -/
theorem middle_terminal_abs_gap :
    absDiff 240172 (4*60031) <= 145 := by
  decide

/-- The preceding root-ray bridge has the exact allowed error c=5, e=306. -/
theorem preceding_root_ray_bridge :
    -(306:Int) <=
      (240172:Int)-4*(60031:Int)-(5:Int)-((260178:Int)-13*(20001:Int)) /\
    (240172:Int)-4*(60031:Int)-(5:Int)-((260178:Int)-13*(20001:Int)) <= 306 := by
  decide

/-- The existing cancellation adapter really does put the predecessor in
logOuterBudget at exponent n+6=16. -/
theorem predecessor_in_log_budget :
    logOuterBudget 260178 20001 16 := by
  exact far_far_terminal_to_logOuterBudget
    10 260178 20001 240172 60031 145 306 5
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    middle_terminal_abs_gap
    (by decide) (by decide)

/-- The budget, source-certified terminal ratio window, and three-step
halting path coexist.  This is a counterexample to any general theorem that
the derived log budget alone forces a third successful transition. -/
theorem budgeted_three_step_halt :
    logOuterBudget 260178 20001 16 /\
    highLevelNext (.D 260178 20001) = some (.D 240172 60031) /\
    highLevelNext (.D 240172 60031) = some (.D 180132 180131) /\
    highLevelNext (.D 180132 180131) = none := by
  exact ⟨predecessor_in_log_budget, predecessor_to_middle,
    middle_to_terminal, terminal_halts⟩

#print axioms predecessor_root_band
#print axioms middle_terminal_ratio4_window
#print axioms predecessor_to_middle
#print axioms middle_to_terminal
#print axioms terminal_halts
#print axioms predecessor_in_log_budget
#print axioms budgeted_three_step_halt

end BB6.Agent48TerminalBudgetCounterexample
