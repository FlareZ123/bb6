import RootSourceBridge
import Q4RightEndpoint
import S1CountedDrain

/-!
# TM63 blank-root q4 all-ones drain prefix

Compose the kernel-checked 27,959-step blank-root-to-S1 prefix, the
source-level 332-step q4 transition, and the parity-complete all-ones S1
drain.  This is an exact original-table run prefix.  It does not assert
that the endpoint halts or that TM63 is the six-state champion.
-/

namespace BB6Coverage.Agent48CountedInc0

open BB6Coverage
open BB6Coverage.Agent42InitialS1Root
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent8S1Encoder

/-- Exact source cost of draining the 63-bit all-ones counter. -/
def q4DrainMoves : Nat := 6*4^63 + 42*2^63 - 12*63 - 48

/-- Complete certified run length from the genuine blank root through
    the q4 suffix and the subsequent all-ones drain. -/
def rootQ4DrainMoves : Nat := 27959 + (332 + q4DrainMoves)

/-- The closed form simplifies to 6*4^63 + 42*2^63 + 27487 moves. -/
theorem rootQ4DrainMoves_closed :
    rootQ4DrainMoves = 6*4^63 + 42*2^63 + 27487 := by
  decide

/-- The original TM63 table executes the entire root-connected q4 drain
    from the blank tape, ending at the canonical S1 state with the left
    counter zero and the right unary counter 2^63-1. -/
theorem tm2_blank_reaches_q4_drain_endpoint :
    run tm2 rootQ4DrainMoves blank =
      some (s1Config 3 6 1 71 0 (2^63-1) 223) := by
  have hroot := tm2_blank_reaches_initialS1_source
  have hq4 := tm2_q4_root_source
  have hbound : 2^63-1 < 2^71 := by decide
  have hdrain := s1Config_counted_drain_closed 3 6 1 71 63 223 hbound
  unfold rootQ4DrainMoves
  rw [run_add tm2 blank 27959 (332+q4DrainMoves)]
  rw [hroot]
  rw [run_add tm2 rootS1Config 332 q4DrainMoves]
  rw [hq4]
  simpa [q4DrainMoves] using hdrain

#print axioms rootQ4DrainMoves_closed
#print axioms tm2_blank_reaches_q4_drain_endpoint

end BB6Coverage.Agent48CountedInc0
