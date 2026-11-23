import NineteenthFastPrefix

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast BB6.DRegularFastSmall

/-- Exact 9,780-step terminal certificate, composed from the three existing
    source-checked blocks (4,096 + 4,096 + 1,588). -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  have hlen : 9780 = 512*16+1588 := by decide
  rw [hlen]
  rw [run_blockedWith 512 16 1588 seed19 seed19_canon]
  rw [fast512_16_seed19]
  exact terminal1588_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
