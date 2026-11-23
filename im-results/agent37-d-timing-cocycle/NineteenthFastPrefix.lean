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
  cases hopt : fastRunBlocksWith 512 8 seed19 with
  | none => simp [hopt] at h
  | some x =>
      simp [hopt] at h
      cases h
      rfl

/-- Reuse the already certified second 4,096-step block. -/
theorem fast512_8_block19_1 :
    fastRunBlocksWith 512 8 block19_1 = some block19_2 := by
  have h := run_blockedWith 512 8 0 block19_1 block19_1_canon
  have hlen : 512*8+0 = 4096 := by decide
  rw [hlen, block19_2_exact] at h
  cases hopt : fastRunBlocksWith 512 8 block19_1 with
  | none => simp [hopt] at h
  | some x =>
      simp [hopt] at h
      cases h
      rfl

/-- The two certified 4,096-step blocks combine to the 8,192-step prefix. -/
theorem fast512_16_seed19 :
    fastRunBlocksWith 512 16 seed19 = some block19_2 := by
  rw [show 16 = 8+8 by decide, fastRunBlocksWith_add]
  simp [fast512_8_seed19, fast512_8_block19_1]

#print axioms fast512_8_seed19
#print axioms fast512_8_block19_1
#print axioms fast512_16_seed19

end BB6.Agent2NineteenthRoot
