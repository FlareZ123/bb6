# Raw124 F1=0LA: deferred standalone scan

**Status: not run to completion; do not treat as a result or proof.**

Exact child table:
`1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LA`

A standalone cap-3000/lookback-32 fast-partition plus six-state FAR scan was implemented in `scan_0la.py` and exposed as workflow target `weighted-tnf-raw124-0la-scan`. Run `45827823002` was cancelled at 2026-11-26T13:26:21.391Z after inspecting Agent2's persistent memory: its 2026-11-26 08:03 checkpoint already records a combined local partition for the four unfinished Raw124 F1 siblings 0LA/0LB/0LE/0LF (16,052 open leaves, 15,195 pooled FAR closures, 288 residual candidates in local scratch `/tmp/raw124new`). Repeating a separate 0LA scan would be redundant unless that combined partition cannot be recovered or Agent2 requests an independent reproduction.

Next use: ask Agent2 for the exact persisted 0LA table/open-list/witness data or a specific subset of the 288 residuals to solve. Only dispatch the standalone scan if the prior combined work is unavailable and ownership is coordinated.

The scan script is discovery infrastructure only. Even if it runs, its output must be converted to an exact disjoint Lean `Audit` tree and checked against original sources before any bound claim.
