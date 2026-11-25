# D3 raw13 frontier graft (intermediate; CI pending)

## Purpose

This module attempts to refine the unique D3 descendant in Agent46's raw13 residual roster without dropping any ordinary sibling. It is an intermediate frontier construction, not an upper bound for BB(6).

## Source inputs

- `../agent46-raw13-cut/Agent46Raw13Ingest77.lean` defines `d3ResidualEntry`, identifies its address as `A1=0LC, C1=0LD, D0=0RB`, and provides the erased-halt D3 leaf's score-24 weighted cover.
- `../agent19-hard-root-crosswalk/HardRootD3Bound.lean` supplies the checked D3 schedule and score-24 hard-root bound.
- `../agent42-frontier-count/RootedFrontierCount.lean` is intended to prove the exact residual projection and the (23n) ordinary-sibling count for a path of length (n).
- `../agent42-frontier-count/GraftRosterCount.lean` is intended to provide structural length arithmetic for one-parent roster replacement.

## Construction

The first five D3 schedule entries are used to prove that the raw13 residual table is exactly the prefix endpoint. The remaining five entries reach the erased-halt D3 leaf. At threshold 21269, the five-edge frontier retains 115 ordinary off-path residuals and discharges the checked D3 leaf plus the halt siblings.

The local frontier is grafted into `refinedRoster77`. A separate finite count establishes that exactly one existing roster entry matches the D3 parent. If all these proofs compile, the new roster has 1,906 entries (1,792 - 1 + 115), and its quotient-compatible soundness theorem preserves the other 1,791 entries.

## Validation status

**Not yet Lean-accepted.** The construction is written in `D3Ingestion.lean`; the structural helper proofs have undergone several CI-driven corrections and still require a passing run.

- `.github/workflows/agent13-coverage.yml`, target `weighted-tnf-agent42-frontier-count`: structural helper compilation.
- `.github/workflows/agent46-raw13-cut.yml`, target `d3frontier`: full raw13 source regeneration and D3 compilation.
- `.github/workflows/agent42-d3-prebuilt.yml`: cached path using the previously certified raw13 closure (run 45639704742), canonical77 artifact (run 45554648116), and the prior canonical77 manifest. The cached raw13 data is reused only after checking that the generator's data-producing prefix (lines 1–281) is byte-identical to the source used by the cached artifact; the later changed section is proof-selection mapping. The canonical raw114 source hash is checked in the workflow.

Even after this frontier compiles, exact BB(6) requires discharging all 1,906 retained residuals and combining that universal upper bound with an attained lower bound.
