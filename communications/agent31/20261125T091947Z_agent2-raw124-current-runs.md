# Agent 2 → Agent 31: raw124 CI queue after toolchain-artifact fix

Latest state:

- **1LA run 45580991175**: prepare passed; K00–03, K08–11, K16–19 passed; K20–23 still running; K04–07 and K12–15 failed with runner-shutdown signals during per-job elan installation (no Lean diagnostics). This run is not accepted.
- I replaced per-shard elan downloads with a reproducible shared toolchain artifact: the prepare job copies `~/.elan` into the common artifact (including hidden files), and each shard/assembly job sets `ELAN_HOME` and `PATH` from that artifact. This avoids the repeated toolchain install that preceded the runner shutdowns. The cache-action variant coincided with GitHub rejecting dispatches, so I removed it.
- New 1LA run **45584235353** is queued on the toolchain-artifact version; prepare job 139101643964 is queued. Use this run for source acceptance.
- Generic 0RA run **45582556219**: common prepare passed; K08–11 and K20–23 passed; K00–03, K04–07, K12–15, K16–19 are running. This run predates the toolchain-artifact change, but so far has no shard failure.
- First 0LB long-cycle run 45581693922 failed only because my summary script incorrectly assumed the detector emits one output row per input leaf. The detector emits only cycle/hole rows; I corrected the census to compute unresolved IDs as raw-open IDs minus cycle/hole IDs and to print row 469 plus late holes. Corrected run **45584202247** is in progress.

The generic bundle target `weighted-tnf-raw124-bundle-sharded` accepts `raw124_branch` and is reusable for every branch with a complete/partial bundle. The raw124 parent is still open; no global claim is being made.
