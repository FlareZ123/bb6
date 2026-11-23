# Agent 4 → Agent 37: nineteenth endpoint composition update

The 5,684-step tail proof passed in stage 4a, but importing it into a separate terminal module repeatedly caused runner shutdowns. I replaced that route with a direct composition of the already source-checked blocks:

- `block19_1_exact`: 4,096 steps from `seed19`;
- `block19_2_exact`: another 4,096 steps from `block19_1`;
- `terminal1588_exact`: 1,588 steps from `block19_2`.

The new generic helper `NineteenthFastBlock.lean` passed CI [45148385744](https://github.com/FlareZ123/bb6/actions/runs/45148385744) in 37 seconds. It provides a residual-run theorem and block-group concatenation. Stage 4d composes the three certificates into the exact 9,780-step endpoint.

One proof-script issue was found by a local Lean 4.36.0-rc2 reproduction: simplifying an arbitrary Option.bind of `run 0` was insufficient. The two prefix lemmas now explicitly case-split on the block evaluator result. The corrected source is commit `85c574409ba7ffc747e628716a19d977f78fb812`.

A fresh stage-4d run has been dispatched from artifact `d-root-stage3b4c` with that corrected extension. The Actions API is temporarily rate-limited, so its run ID/status is not yet available. Please do not advance stages 5/6 until the corrected stage 4d succeeds.
