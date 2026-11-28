# Raw34 D1=1RD: original-source proofs and exact residual frontier

**28 November 2026.** Research result: **4,713,281,250 disjoint physical completions are now covered by original-source Lean nonhalting or weighted bounded-halting certificates** of the Raw34 subbranch D1=`1RD`, with **1,390,234,375** not covered by this proof bank. Full Raw34 / BB(6) exactness remains open. See the [publishable mathematical synthesis](../../results/2026-11-28-raw34-d1rd-certified-cylinders-agent23.md) for source theorem names, CI, proof boundary and exact disjoint cardinalities.

## Reproducible source and finite physical frontier

The parent partial table is `1RB---_1RC---_0RD---_1LC---_------_------`; D1=`1RD` fixes five actions, leaving seven positions and 25^7=6,103,515,625 physical machines. The [source-certificate frontier](D1-1RD-proof-frontier.json), rebuilt by [`export.mjs`](export.mjs), partitions exactly into 124 old-proof-covered leaves (**3,320,312,500**) and 165 disjoint old-proof-uncovered leaves (**2,783,203,125**). Its 3,087 source cylinders come from Agent50's accepted Raw34 proof bank. Every covered leaf is source-contained, every open leaf is disjoint from each original source cylinder, every pair of leaves is disjoint, and the 25-ary masses are conserved.

Twelve of the 165 open leaves have assigned HALTs before reaching any unknown transition, source-accepted as `Cover (WeightedBound 18)` in [`Raw34D1RDHalting12.lean`](Raw34D1RDHalting12.lean), [CI 46096340042](https://github.com/FlareZ123/bb6/actions/runs/46096340042): **351,562,500** completions. The individual genuine query traces are [`halting12.json`](halting12.json).

The other 153 open leaves expand by their **first genuinely missing queried instruction** into exactly 3,825 physical subcylinders in [`one-step-refine.json`](one-step-refine.json), rebuilt by [`next-stage.mjs`](next-stage.mjs). One further assignment yields 153 source-checked halters, **97,265,625** completions, and 1,744 source-checked oriented side cycles, **934,375,000** completions. All 1,897 are Lean-accepted through the original-source [`Raw34D1RDOneStepCore.lean`](Raw34D1RDOneStepCore.lean) and 16 [`Raw34D1RDOneStepShard00..15.lean`](.) theorem banks: [CI 46097309170](https://github.com/FlareZ123/bb6/actions/runs/46097309170). A small 31-witness [pilot](Raw34D1RDOneStepPilot.lean) is independently source-accepted in [CI 46097305249](https://github.com/FlareZ123/bb6/actions/runs/46097305249).

A new unbounded quadratic-growth pump `1RB---_1RC---_0RD0RF_1LC1RD_------_---1LD` is proved `NeverHalts` for all compatible completions in [`Raw34TripleSweepGrowthF.lean`](Raw34TripleSweepGrowthF.lean), [CI 46097305249](https://github.com/FlareZ123/bb6/actions/runs/46097305249). Its separate five-hole cylinder contributes **9,765,625** disjoint completions.

**Next pending original-source proof**: [`Raw34D1RDDepth2C1RF.lean`](Raw34D1RDDepth2C1RF.lean) has 159 second-unknown side-cycle/halting candidates, **62,109,375** completions, not included in the accepted total unless its dedicated CI passes. Full [candidate data](depth2-C1-0RF.json).

## Precision and limitations

The original Lean theorems establish nonhalting or sufficient weighted bounds for each literal partial machine. The finite exact union and complementary frontier are currently audited by JavaScript **not by an aggregate Lean `Cover` consumer**. In particular, the 1,390,234,375 residual completions are not proved to halt or not halt, and these results do not establish a complete Raw34 Cover, global BB(6) upper bound or Canonical40 reduction.

A physical `HALT` instruction is **not** the wildcard `---`. The two JSONs' per-slot `decisions` or `action` fields are authoritative. A `projection` may show HALT as `---` solely for display; never use the projection alone to identify the cylinder. The accepted pre-existing triple sweep `pA` fixes A1=1LD; omitting it would falsely increase the old nonhalting union.
