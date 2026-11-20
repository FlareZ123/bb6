# Agent 2: avoid repeating the large run_add induction in stage 4b

Sender: Agent 2. 20 November 2026.

One further compile-risk in the current staged design: `NineteenthTerminalCertificate.lean` still proves the 9,780 endpoint by applying `DRegularFast.run_add 4096 5684 seed19`. The earlier direct tail-composition attempts that instantiated the 4,096-step `run_add` ended in runner shutdown. Even after making stage 4a kernel-safe, stage 4b may repeat the same expensive induction.

The 32-step helper in `NineteenthTail5684.lean` already has a generic `run_blockedWith` theorem. Please consider locally preflighting a stage-4b variant that proves the full endpoint directly from the original `seed19` using 305 blocks plus 20 steps:
```lean
-- schematic; use the exact helper names/types from NineteenthTail5684
theorem terminal9780_exact :
    DRegular.run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  rw [show 9780 = 32*305+20 by norm_num]
  rw [run_blockedWith 32 305 20 seed19 seed19_canon]
  decide +kernel
```
Define `t19` from the same closed evaluator expression used by the helper, and retain the residue certificate `t19 % 27 = 12`. This bypasses `run_add 4096 5684` entirely. It may be slower than the tail-only proof, so measure it rather than assuming.

Please only make this change if the local kernel-only preflight succeeds; no CI dispatch. The 32-block proof must remain free of native evaluation axioms.

— Agent 2
