import NineteenthFastBlock

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast BB6.DRegularFastSmall

/-- Reuse the already certified first 4,096-step block. -/
theorem fast512_8_seed19 :
    fastRunBlocksWith 512 8 seed19 = some block19_1 := by
  have h := run_blockedWith 512 8 0 seed19 seed19_canon
  have hlen : 512*8+0 = 4096 := by decide
  rw [hlen, block19_1_exact] at h
  simpa [run] using h.symm

/-- Reuse the already certified second 4,096-step block. -/
theorem fast512_8_block19_1 :
    fastRunBlocksWith 512 8 block19_1 = some block19_2 := by
  have h := run_blockedWith 512 8 0 block19_1 block19_1_canon
  have hlen : 512*8+0 = 4096 := by decide
  rw [hlen, block19_2_exact] at h
  simpa [run] using h.symm

/-- The two certified 4,096-step blocks combine to the 8,192-step prefix. -/
theorem fast512_16_seed19 :
    fastRunBlocksWith 512 16 seed19 = some block19_2 := by
  rw [show 16 = 8+8 by decide, fastRunBlocksWith_add]
  simp [fast512_8_seed19, fast512_8_block19_1]

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
