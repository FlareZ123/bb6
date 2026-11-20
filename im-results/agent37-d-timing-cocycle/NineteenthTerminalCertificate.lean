import NineteenthTail5684
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular

/-- Exact 9,780-section DRegular endpoint, assembled from the 4,096-section
    first checkpoint and the independently checked 5,684-section tail. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  have hlen : 9780 = 4096+(4096+1588) := by omega
  calc
    run 9780 seed19 = run (4096+(4096+1588)) seed19 :=
      congrArg (fun n => run n seed19) hlen
    _ = (run 4096 seed19).bind (run (4096+1588)) :=
      BB6.DRegularFast.run_add 4096 (4096+1588) seed19
    _ = (some block19_1).bind (run (4096+1588)) := by rw [block19_1_exact]
    _ = run (4096+1588) block19_1 := rfl
    _ = some ⟨9*t19+10,9,1⟩ := tail5684_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
