import ExecutableReturn
set_option maxHeartbeats 0
namespace CascadeFastReturn
open CascadeResetInverse CascadeRank CascadeSweep CascadeManyShield

/-- Executable reset-step iteration of the actual source first-reset map. -/
def runFast (start : Nat) : Nat → Option Nat
  | 0 => some start
  | n+1 => (runFast start n).bind fastOutcome

/-- The executable deterministic reset iterator agrees exactly with the
    source-first-outcome selector at every finite length. -/
theorem runFast_eq_runResets (start steps : Nat) :
    runFast start steps = runResets start steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [runFast,runResets,ih]
    cases h : runResets start steps with
    | none => rfl
    | some u =>
      simp [fastOutcome_eq_nextReset]

/-- Source-root reachability of every #746 candidate fatal reset has a
    finite polynomially bounded certificate using a *computable* and fully
    source-sound forward reset function. -/
theorem root_fatal_iff_bounded_executable_run (n : Nat) (hn : 2≤n) :
    ReachC (2,0) (fatal n,0) ↔
      ∃ steps, steps≤(n+2)^2 ∧ runFast 2 steps = some (fatal n) := by
  rw [root_fatal_iff_bounded_forward_run n hn]
  simp only [runFast_eq_runResets]

#print axioms runFast_eq_runResets
#print axioms root_fatal_iff_bounded_executable_run
end CascadeFastReturn
