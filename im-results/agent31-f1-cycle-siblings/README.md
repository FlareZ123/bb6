# Raw139 F/1 cycle siblings — candidate source certificates

This intermediate package records eight complete cycle siblings discovered by the exact finite first-hole scan for the raw139 champion-compatible parent

`[7,24,11,24,14,21,3,16,12,11,24,24]`.

Each sibling fixes only F/1 and retains the other three holes. The scan's cycle witnesses are encoded as `Audit.cycle` leaves and checked by the original `FastThreeHoleAudit.fastCheck` in `ChampionF1CycleSiblings.lean`.

| F/1 child | code | cycle audit (entry, period, right, boundary) |
|---|---:|---|
| 0RA | 1 | (0, 13, true, -2) |
| 0LB | 4 | (2, 18, false, 2) |
| 1RB | 7 | (2, 20, false, 4) |
| 0LC | 8 | (2, 14, false, 2) |
| 1LC | 10 | (2, 14, false, 2) |
| 1RC | 11 | (2, 16, false, 3) |
| 0LE | 16 | (2, 14, false, 2) |
| 1LE | 18 | (2, 14, false, 2) |

The scan was cross-checked against the existing ZeroLD candidate: it reproduced exactly 9 splits, 117 translated cycles, 54 last-hole leaves, 5 FAR leaves, and 32 open leaves at the published 600-step / width-3 settings. This is a validation of the scan implementation, not a substitute for the Lean audit.

**Status: pending original-source Lean CI.** If accepted, these are complete WeightedBound(6) covers for all compatible completions of their eight exact cylinders. The integration consumer now layers these eight parents on the 106-leaf frontier after the 0LF, 1LA, and 0RC grafts. It expects a 98-leaf residual list, but this remains conditional until the exact parent-membership/count theorem and original-source CI pass. No BB(6) upper bound is claimed.

## Integration and next sibling search

- `ChampionF1CycleIntegration.lean` now layers the eight cycle parents onto Agent 6's 106-leaf frontier after the 0LF, 1LA, and 0RC integrations. It asserts eight exact parent memberships and a 98-leaf residual count. This is conditional until the source audit and full-chain CI pass.
- The separate F/1=1LD sibling (code 14) is being explored by `discover_oneLD.py` using the existing Agent48 scanner and pump search, with width-4 FAR search and a 600-step first-hole limit. Workflow: `.github/workflows/agent31-f1-oneLD-discovery.yml`. A Lean package is generated only if every open leaf receives a pump witness.
- Cycle sibling source audit workflow: `.github/workflows/agent31-f1-cycle-siblings.yml`. Current run: [45618644127](https://github.com/FlareZ123/bb6/actions/runs/45618644127). The earlier run failed because the module omitted the `F0SiblingCover` and `BB6.Agent31ThreeHole` imports; those imports have been added for the current run.
- F/1=1LD discovery run: [45618468915](https://github.com/FlareZ123/bb6/actions/runs/45618468915).
