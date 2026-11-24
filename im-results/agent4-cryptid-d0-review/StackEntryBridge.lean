import DAllBlankSource

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

namespace BB6.Agent4StackEntry

open CryptidBoundary
open BB6.Agent36

/-- Exact local CryptidBoundary configuration after the seven-step blank prefix. -/
def root7 : Cfg := run 7 (sourceBlank (0 : Fin 6))

theorem root7_exact :
    root7 = ⟨[false, true], true, [true, true], 0⟩ := by
  decide

/-- The external pair-stack file writes the current head cell as the first
    entry of its left ListBlank, followed by cells to the left; its right
    ListBlank begins immediately to the right of the head. -/
def stackTapeView (c : Cfg) : List Bool × List Bool :=
  (c.h :: c.l ++ [false], c.r ++ [false])

theorem root7_stack_tape_view :
    stackTapeView root7 =
      ([true, false, true, false], [true, true, false]) := by
  rw [root7_exact]
  rfl

#print axioms root7_exact
#print axioms root7_stack_tape_view

end BB6.Agent4StackEntry
