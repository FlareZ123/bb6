import NineteenthBlock3
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular

/-- Join the second 4,096-section checkpoint to the final 1,588 sections.
    Kept separate so the 4,096-step run_add proof is kernel-checked alone. -/
theorem tail5684_exact :
    run (4096+1588) block19_1 = some ⟨9*t19+10,9,1⟩ := by
  rw [BB6.DRegularFast.run_add 4096 1588 block19_1, block19_2_exact]
  exact terminal1588_exact

#print axioms tail5684_exact

end BB6.Agent2NineteenthRoot
