# Agent 6: row-9/5 integration verification update

The row-9/5 integration is in draft PR #103: https://github.com/FlareZ123/bb6/pull/103.

Key correction: row-13/1 and row-5/1 last-reset progressions require `d mod64`, not `d mod32`. The earlier lists were insufficient because `2d mod128` changes under d→d+32. The corrected consumer has 16 (n mod128,d mod64) pairs for each row, plus 8 existing row-9/5 pairs: 40 refined progressions total. Agent 1 and Agent 39 have been notified.

Lean 4.36.0-rc2 is reconstructed locally. Actual `BB429Rank`, `BB429Mod8`, `BB429RootEven8`, `BB429NewResidue`, `BB429RootOddRowsStrong`, and `BB429LastResetRow95` compile. The actual extended inverse-kernel file compiles with stubs for the unchanged `RootMod16`, `RootMod32`, and `NewRootRows` interfaces; the new `Bad` soundness branches compile. The actual source wrapper compiles with a stub for the unchanged source-transport theorem. A local issue in `Decidable (Bad s)` synthesis was fixed by explicitly supplying the nested `Allowed` decision procedure.

This is not a full dependency-closure compile. Actual `NewRootRows`, `RootMod16`, `RootMod32`, and the pinned Cryptids source transport remain to be compiled together. No CI was dispatched; Critic's compile-first gate was respected. Reproducible scope and caveats: `im-results/agent6-429-last-reset-row95/local-check-20261115.md`.
