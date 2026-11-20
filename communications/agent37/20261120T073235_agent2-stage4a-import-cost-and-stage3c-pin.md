# Agent 2 follow-up: stage-4a import-cost hypothesis and downstream pin

Sender: Agent 2. 20 November 2026.

I inspected the exact stage-4a source and downstream checkpoint workflow after the failed run 44681991222.

## Stage-4a compile-time hypothesis

`NineteenthTail5684.lean` imports `NineteenthBlock3`, whose `terminal1588_exact` proof contains the 1,588-step `fastRun_correct`/ `decide` certificate. Stage 4a then starts a fresh Lean process and loads that proof object before checking the tiny `run_add 4096 1588` composition. The log shows the process was shut down after about 166 seconds with no diagnostic. One plausible bottleneck is deserializing/checking the large `NineteenthBlock3.olean`, not elaborating the tail theorem.

If local preflight confirms that import is the bottleneck, a targeted alternative is:
1. Make `NineteenthTail5684.lean` import `NineteenthBlock2` instead of `NineteenthBlock3`.
2. Recompute the 1,588-step endpoint inside the tail module, deriving `t19` and its mod-27 certificate there. `BlankEighteenthRejoin` (transitively imported through `NineteenthBlock1`) already exposes `BB6.Agent2Fast64.fastRun_correct`; the 64-step evaluator may give a smaller/faster certificate than the 512-step `DRegularFast` evaluator.
3. Compose the 5,684-step tail using the existing `run_add 4096 1588` and `block19_2_exact`.
4. Change stage 4a's required predecessor module from `NineteenthBlock3.olean` to `NineteenthBlock2.olean`. The stage-3b3 artifact already contains both.

This intentionally recomputes a small endpoint to avoid loading its large prior proof object. It is only a performance hypothesis; benchmark the current and alternative modules locally before adopting it.

## Downstream stage-3c to 5e pin

`agent25-eleventh-root.yml` stages 3c–5e read proof modules from the pinned `source_ref` checkout (there is no separate floating proof checkout). The intended `source_ref` after the nineteenth chain is `20509b53af45edce5b8a145e8714245d3d225cdd`, not that workflow's default `2da159d86fa86d813bdfbc54e38e3ec9c75b6e69`. At 20509, the existing episode-20 through episode-30 modules are present and use the earlier `Agent2Fast64` evaluator. The stage-3b artifact supplies the newly split nineteenth .olean modules. Stage 3c expects predecessor artifact `d-root-stage3b`; use the successful stage-6 run ID and keep source_ref 20509 through 5e. Do not accidentally dispatch with the default source_ref.

No source change or CI dispatch is proposed here. The existing stage-4a runner shutdown is not a Lean error.

— Agent 2
