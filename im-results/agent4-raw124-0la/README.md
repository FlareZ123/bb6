# Raw124 F1=0LA: deferred standalone scan

**Status: not run to completion; do not treat as a result or proof.**

Exact child table:
`1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LA`

A standalone cap-3000/lookback-32 fast-partition plus six-state FAR scan was implemented in `scan_0la.py` and exposed as workflow target `weighted-tnf-raw124-0la-scan`. Run `45827823002` was cancelled at 2026-11-26T13:26:21.391Z after inspecting Agent2's persistent memory: its 2026-11-26 08:03 checkpoint already records a combined local partition for the four unfinished Raw124 F1 siblings 0LA/0LB/0LE/0LF (16,052 open leaves, 15,195 pooled FAR closures, 288 residual candidates in local scratch `/tmp/raw124new`). Repeating a separate 0LA scan would be redundant unless that combined partition cannot be recovered or Agent2 requests an independent reproduction.

Next use: ask Agent2 for the exact persisted 0LA table/open-list/witness data or a specific subset of the 288 residuals to solve. Only dispatch the standalone scan if the prior combined work is unavailable and ownership is coordinated.

The scan script is discovery infrastructure only. Even if it runs, its output must be converted to an exact disjoint Lean `Audit` tree and checked against original sources before any bound claim.


## Persisted-spec replay (2026-11-26)

A committed parameterized witness spec was found at `im-results/agent2-tnf-raw124/sibling-0LA.spec.b64` (Git blob `53b381728a2936793d18284a46f3ea778eb296cb`). Use the existing `replay_fast_cut.py` rather than repeating the standalone discovery scan. It verifies the exact partition-tree and open-list SHA256 values embedded in the spec and re-emits the FAR/growth/parameter certificates.

A source-only replay target, `weighted-tnf-raw124-0la-fast-cut`, is now running as [run 45830548316](https://github.com/FlareZ123/bb6/actions/runs/45830548316). It reuses the accepted Raw124 1LB source core from run 45800254828 and targets `BB6.Agent2Raw124New0LA.branch_sound` plus `residual_count` at weighted bound 3006. Expected artifact name: `raw124-0la-partial-source-audit`.

This is a partial cut only. The number and exact table keys of the remaining one-hole residuals must be taken from the generated `Raw124New0LA.remaining` artifact after the replay succeeds; do not assume the combined four-sibling residual count of 288 belongs entirely to 0LA. No full F1=0LA Cover is claimed.
