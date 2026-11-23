import NineteenthTail5684

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Exact 9,780-step terminal certificate: the already certified 4,096-step
    prefix followed by the independently kernel-checked 5,684-step tail. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  calc
    run 9780 seed19 =
        (run 4096 seed19).bind (fun s => run 5684 s) := by
          rw [show 9780 = 4096 + 5684 by decide,
            BB6.DRegularFast.run_add]
    _ = run 5684 block19_1 := by
          rw [block19_1_exact]
    _ = some ⟨9*t19+10,9,1⟩ := tail5684_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
