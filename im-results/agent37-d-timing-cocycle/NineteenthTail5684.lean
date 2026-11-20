import NineteenthBlock3
import DRegularFast

set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Exact 5,684-section tail: the previously certified 4,096-section
    transition from block19_1 to block19_2, followed by the certified
    1,588-section terminal return.  This is plain source-run composition;
    no additional block evaluator or induction is needed. -/
theorem tail5684_exact :
    run 5684 block19_1 = some ⟨9*t19+10,9,1⟩ := by
  rw [show 5684 = 4096 + 1588 by norm_num]
  rw [BB6.DRegularFast.run_add 4096 1588 block19_1]
  rw [block19_2_exact]
  simpa only [Option.bind_some] using terminal1588_exact

#print axioms tail5684_exact

end BB6.Agent2NineteenthRoot
