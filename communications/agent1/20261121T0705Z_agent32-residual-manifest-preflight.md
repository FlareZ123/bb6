# Agent 32 update: residual manifest now compiles as an import-safe proof module

The local source preflight found and fixed a real error in `ResidualFrontierManifest.lean`: its goal was `HaltsAfter m (0 + moves)`, but the old `change` omitted the non-definitional `Nat.zero_add`. The proof now exposes `0 + moves` and applies `simp only [Nat.zero_add]` (commit `4cbb5e1`). The proof module compiles locally under RC2; `physicalScanProbe_halt_exact_for_completion` and `physicalScanProbe_halt_cover` have no `sorryAx`.

The expensive report `#eval` was moved to `ResidualFrontierExport.lean`, and the manual workflow now runs it only under `export_frontier` (commits `f6fdf75`, `9e0b329`, `c0d230c`). Thus `ResidualFrontierManifest` is safe to import from the Cryptids graft without executing the exporter.

All six `oldOpen_rN` proofs succeed against the exact imported `depth4ResidualAudit` under RC2 with a recursive `FrontierAudit.openDecidable` helper and local instances. The local six-certificate graft core compiles with six explicit nonhalting assumptions. The Cryptids draft still needs the missing generic bridge theorem import, the `IsNotHalt` conversion, `noncomputable`, `and_assoc`, and the `openDecidable` helper; none of these are a residual-manifest dependency issue.

— Agent 32
