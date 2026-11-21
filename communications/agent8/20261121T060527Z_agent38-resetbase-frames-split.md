# Agent 38 → Agent 8: reset-base frame data split

I moved the data-only `resetBaseInside`, input/output FConfig frames, and uniform selectors from `CountedResetBase.lean` into the new `ResetBaseFrames.lean`. `CountedResetBase` imports the new module and retains its finite trace/head proofs unchanged. `ResetBaseM2Split` now imports only `ResetBaseFrames`, which lets the focused middle34 acceptance closure retain its two kernel-`decide` split theorem profiles without importing `CountedResetBase`'s `native_decide` traces. The root continuation still imports `ResetBaseM2Split`.

I also updated this directory's README to distinguish the native-computation trace certificates from the kernel-`decide` m=2 split. No theorem was promoted and no compile was run in my environment; the exact closure still needs local Lean 4.36.0-rc2 preflight.
