import F321BackwardBarrier
import Phase6
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321Phase6Bridge
open BB6.Agent31F321Density
open BB6.Agent2F321Phase6

/-- The local minimal Reach is definitionally the same step system as the
    repository's canonical CounterReach. This transport integrates the new
    Phase6 invariant with all existing F321 source theorems. -/
theorem counterReach_to_reach {n a d : Nat}
    (hr : CounterReach 1 1 n a d) : Reach n a d := by
  induction hr with
  | nil => exact Reach.nil
  | step hr hm ih => exact Reach.step ih hm

theorem counterReach_phase6 {n a d : Nat}
    (hr : CounterReach 1 1 n a d) :
    (n = 0 ∧ a = 1 ∧ d = 1) ∨ Phase6 a d :=
  root_phase6 (counterReach_to_reach hr)

/-- Canonical CounterReach terminal consequence. -/
theorem counterReach_terminal_mod6 {n d : Nat}
    (hn : 0 < n) (hr : CounterReach 1 1 n (d+1) d) : d % 6 = 1 :=
  terminal_phase6 hn (counterReach_to_reach hr)

/-- Canonical CounterReach version of the reachable middle-odd predecessor
    shape used by the reset-to-reset analysis. -/
theorem counterReach_middleOdd_shape {n a d : Nat}
    (hr : CounterReach 1 1 n a d) (h1 : a < d) (hp : (d-a)%2 = 1) :
    a % 2 = 0 ∧ d % 6 = 1 :=
  reachable_middleOdd_shape (counterReach_to_reach hr) h1 hp

#print axioms counterReach_to_reach
#print axioms counterReach_phase6
#print axioms counterReach_terminal_mod6
#print axioms counterReach_middleOdd_shape
end BB6.Agent2F321Phase6Bridge
