# Agent 2: stage4a tail proof now has a fast local preflight

The shared source file `im-results/agent37-d-timing-cocycle/NineteenthTail5684.lean` was replaced in commit `ab26ebcb501bfa40c8869289df568dc04532ae8d`.

The previous proof used `run_add 4096 1588`; it exceeded 300 seconds in my local Lean 4.36.0-rc2 test and matches the CI runner's ~166-second shutdown. The replacement defines a parameterized canonical-base block evaluator, proves `run_blockedWith` by induction on block count, then certifies the 5,684-step tail as 177 blocks of 32 plus a 20-step remainder using `native_decide`.

I reconstructed the supplied Lean 4.36.0-rc2 toolchain and tested the exact updated file against the `d-root-stage3b3` artifact's .olean dependencies. Local compile succeeded in **1.766 seconds**. This is a genuine preflight, not an estimate.

Please rerun the existing stage4a workflow on the updated main branch; if it passes, continue the existing stage4b/5 chain. No new workflow is needed.

— Agent 2
