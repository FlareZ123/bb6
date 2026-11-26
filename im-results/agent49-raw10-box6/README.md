# Raw10 original-source box 6 closure

The original-source rectangle at `raw10Remainder[6]!` has a source-accepted weighted closure at bound 75. The source consumer exposes:

- `BB6.Agent49Box6.box6_weighted`: for `Fits BB6.Agent49Box6.baseBox m`, proves `WeightedBound B m` whenever `75 ≤ B`.
- `BB6.Agent49Box6.raw10_box6_closed`: identifies a source-matched member of `raw10Remainder` and supplies the same weighted closure.
- The source proof's eight audited theorem interfaces use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide`.

## Reproducible artifacts

Run [45898296738](https://github.com/FlareZ123/bb6/actions/runs/45898296738) succeeded and uploaded `raw10-box6-source-closure` (artifact ID `15155195350`, 209,883,455 bytes, SHA-256 `7074af84540abfd6689c90386d4ef882649269f5b662ae10c6809d1be0c963df`, retained to 2026-12-26). It contains the source/import/olean manifest and the compiled source closure.

The same run compiled the thin Box6 consumer against the Box5/7 precompiled artifact: 127 modules were reused, 164 project modules were present in the resulting closure, and all 94 shared modules matched the independently generated Box6 manifest with zero identity mismatches and zero provenance differences. The probe source is [`Raw10RefinedBox6Probe.lean`](../agent49-raw10-refined-cut/Raw10RefinedBox6Probe.lean).

## Refined Raw10 parent-cut effect

Kernel-evaluated probe counts show that adding original-source Box6 after accepted Box5, Box7, Box8, and Box18–24 leaves **30 open rectangles**. With the separate Box16/17 candidate bounds, the candidate cut leaves **28**. These counts are exact evaluations of the repository's finite rectangle lists.

The final adapter is in [`Raw10RefinedBox6.lean`](../agent49-raw10-refined-cut/Raw10RefinedBox6.lean). It proves the source `baseBox` is `raw10Remainder[6]!` by `decide`, transfers the weighted bound, and constructs conditional parent Covers with 30 and 28 open rectangles. Its compilation and axiom audit are running in [45899419790](https://github.com/FlareZ123/bb6/actions/runs/45899419790); until that run succeeds, treat the wrapper as pending.

This is not a complete Raw10 parent Cover. The remaining open rectangles and the held-leaf premise still need proofs, and the 28-open candidate retains explicit Box16/17 bound parameters.
