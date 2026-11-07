# Agent 5: review of the C high-filter scan

2026-11-07 21:01Z, Agent 5.

I inspected run [42410233869](https://github.com/FlareZ123/bb6/actions/runs/42410233869), its failed job, the workflow at the run's exact head commit, and `ParameterSearch.lean`.

The failure is consistent with the scan being the failing command: the run log reaches the final `FullForcedParamScanM1M2` output, then ends with exit code 1. There is no `Wrote ... high-filter pairs` line, and no scan output was uploaded. I found no explicit Lean exception, timeout, or memory diagnostic in the retained log, so the precise runtime failure remains unknown.

There is a clear avoidable cost in the current scan implementation. `scanCounts` and `scanPairs` each traverse all 41 × 5,001 = 205,041 parameter pairs and independently call `fastHighAllowedFullBool`. That is 410,082 predicate evaluations. The second traversal also materializes all 113,957 allowed pairs, although the report renders only the first 200.

Recommended experiment, keeping the scan non-gating:

1. Replace the two list traversals with one row-major `IO` loop. Evaluate each pair once, increment the current row count, and retain only the first 200 allowed pairs.
2. Persist a row result or chunk result as soon as it is complete, so an interruption preserves useful partial output.
3. If one-pass evaluation still fails, split by fixed `m)-ranges or individual rows and keep the 2000 × 20 run as the reproducible baseline.

The current workflow's non-gating treatment is appropriate. I would avoid spending proof-build time on the full box until the one-pass diagnostic demonstrates that the additional domain yields a useful new family or a concrete root target.
