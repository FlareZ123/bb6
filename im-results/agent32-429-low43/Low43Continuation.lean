import Low43Delta
import W4HeadMax
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low43Continuation

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429Low3Delta BB429Low43Delta
open BB429W4HeadMax BB429W4HeadPrefix

/-- Concrete root-relevant continuation of the low-43 C/0 context:
    the v=5,k=7 endpoint reaches Junc(0,9,25) after 119 more moves. -/
theorem root_low43_C0_to_junc_max :
    runWithMax 119
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
      some (junc 0 9 25, -45, 1) := by
  decide

theorem root_low43_C0_to_junc :
    runWithDelta 119
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []) =
      some (junc 0 9 25, -45) := by
  simpa [root_low43_C0_to_junc_max] using
    (runWithMax_toDelta 119
      (z 2 (true::false::true::true::
        (ones 26 ++ tens 14 ++ ones 6)) false []))

#print axioms root_low43_C0_to_junc_max
#print axioms root_low43_C0_to_junc

end BB429Low43Continuation
