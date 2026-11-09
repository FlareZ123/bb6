import W2CZeroEvents
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2EvenEvent
open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429W4CZeroCount BB429W2CZeroEvents

/-- Every even parameter v=2k, including v=0, has a second C/0 at exactly
    34k+164 executed primitive moves. Its right tape is blank and
    exactly one prior C/0 has been executed. -/
theorem even_w2_all_second_gate (k : Nat) :
    (runCount (34*k+164) (junc 0 (2*k) 2)).map
      (fun p => (p.1.state,p.1.current,p.1.right,p.2)) =
    some (2,false,[],1) := by
  cases k with
  | zero => decide
  | succ k =>
      rw [show 34*(k+1)+164 = 34*k+198 by omega,
          show 2*(k+1) = 2*k+2 by omega,
          junc0_w2_even_second_gate_count]
      rfl

#print axioms even_w2_all_second_gate

end BB429W2EvenEvent
