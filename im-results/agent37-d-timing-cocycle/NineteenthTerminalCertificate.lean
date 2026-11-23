import NineteenthTail5684
import DRegularFast

set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Exact 9,780-section endpoint, composed from the certified 4,096-step
    prefix and the kernel-checked 5,684-step tail. The final axiom audit is
    transitive through tail5684_exact. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  rw [show 9780 = 4096 + 5684 by decide]
  rw [BB6.DRegularFast.run_add 4096 5684 seed19]
  rw [block19_1_exact]
  simpa only [Option.bind_some] using tail5684_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
