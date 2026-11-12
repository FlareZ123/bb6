# Fixed counted-carry boundary traces

This directory contains finite source-exact TM63 transition traces that sit
around the four residue bridges in
`im-results/agent24-champion-time/CountedCarryBridges.lean`.

## Proven traces

The module
[`CountedCarryBoundaryTraces.lean`](CountedCarryBoundaryTraces.lean)
imports the existing finite-run and arbitrary-exterior frame machinery. It
proves three additional traces from the actual `tm2` transition table:

| Trace | Initial finite configuration | Final finite configuration | Moves |
|---|---|---|---:|
| A→D scan | A/head 0, ones at 1,…,12 | D/head 12, ones at 0,3,6,9,12 | 12 |
| D-tail15 | D/head 0, ones at 0,…,6 | E/head 9, ones at 0,3,4,5,6,8 | 15 |
| exceptional A→A return | A/head 0, ones at -3,-2,-1,1,…,6 | A/head 6, ones at -3,-2,-1,0,3,4,5,7 | 12 |

The finite configurations use the source `FConfig` list representation;
the physical marked-cell sets are shown in the table. The final list order is
retained exactly as produced by `fRun`, so the finite-run equalities are
kernel checked rather than merely set-equivalent.

Each trace has both a finite-window frame theorem and an arbitrary-exterior,
arbitrary-head lift:
- `carryAD12_trace` / `carryAD12`
- `carryDTail15_trace` / `carryDTail15`
- `carryAReturn12_trace` / `carryAReturn12`

The lift uses the existing `carryBridgeLift` theorem. Its explicit local
match premise is what allows the exterior tape to remain arbitrary; the
theorems do not silently assume a blank exterior.

The module also proves `carryBridge3_matches_carryAD12`: after the existing
rho=3 residue bridge, the framed A-state already supplies the first three
ones in the A→D input window. If the untouched exterior has ones at
`h+2,…,h+10`, the entire A→D 12-cell local window matches. This is the
first explicit composition interface between the existing residue-3 bridge
and the new A→D trace; the later right-run and zero-boundary conditions are
still separate obligations.

## Verification

The selective, fail-closed source workflow
[`agent42-champion-terminal-source.yml`](../../.github/workflows/agent42-champion-terminal-source.yml)
compiles the original machine source, the four existing residue bridges, and
this module with Lean **4.36.0-rc2**.

[CI 43167823012](https://github.com/FlareZ123/bb6/actions/runs/43167823012)
and [CI 43168841419](https://github.com/FlareZ123/bb6/actions/runs/43168841419)
completed successfully. All trace/lift theorem audits, including `carryBridge3_matches_carryAD12`, are
`[propext, Classical.choice, Quot.sound]`; none contains `sorryAx`.

## What remains

These are fixed boundary traces, not the arbitrary-`r` counted-carry
theorem. The next composition is the exceptional `rho=3` branch:
- for the short `t=1` case, compose the residue-3 bridge with
  `carryAReturn12`;
- for `t≥2`, compose the residue-3 bridge, `carryAD12`,
  `counted_right_sweep (4*(t-2))`, and `carryDTail15`.

That composition still needs its local input matches, the contiguous
right-run premise, and the three-cell zero boundary derived from the
original encoded tape. Do not treat those premises as established here.
