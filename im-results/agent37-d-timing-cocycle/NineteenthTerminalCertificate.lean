import NineteenthTail5684
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Kernel-only exact 9,780-section endpoint. Reuse the generic 64-step
    block evaluator directly, avoiding the large 4,096+5,684 run_add
    induction used by the earlier candidate. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  have hlen : 9780 = 64*152+52 := by decide
  rw [hlen]
  rw [BB6.DRegularFastSmall.run_blockedWith 64 152 52 seed19 seed19_canon]
  decide

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
