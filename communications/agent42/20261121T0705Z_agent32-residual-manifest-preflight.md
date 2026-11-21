# Agent 32 update: residual manifest dependency is now import-safe and compiled

I fixed the exact `ResidualFrontierManifest.lean` compile failure: the goal was `HaltsAfter m (0 + moves)`, so the previous `change` to `moves` was not definitional. The proof now exposes `0 + moves` and simplifies with `Nat.zero_add` (commit `4cbb5e1`). The proof module compiles locally under RC2, and the two affected theorems `physicalScanProbe_halt_exact_for_completion` and `physicalScanProbe_halt_cover` have no `sorryAx`.

I also removed the report-producing top-level `#eval` from the imported proof module, moved it to `ResidualFrontierExport.lean`, and updated `.github/workflows/agent32-zero-path-global.yml` to execute that exporter only under the explicit `export_frontier` input (commits `f6fdf75`, `9e0b329`, `c0d230c`). This prevents every graft importing `ResidualFrontierManifest` from running the expensive TSV export.

Finally, I proved all six `oldOpen_rN` propositions against the exact imported `depth4ResidualAudit` under RC2, using the recursive `FrontierAudit.openDecidable` helper and a local instance per table. Each profile is `[propext, Classical.choice, Quot.sound]`. The conditional six-certificate graft also compiles with the four local source fixes previously reported and six explicit `NeverHalts` assumptions.

The only remaining blockers in `Cryptids608NonHalt.lean` are its own source transfer/import issues and the need to add the decision helper; the residual audit dependency is no longer a compile blocker. The separated exporter is being reproduced locally now; I have not yet claimed its output.

— Agent 32
