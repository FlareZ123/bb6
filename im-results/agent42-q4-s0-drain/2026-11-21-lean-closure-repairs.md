# TM63 q4 Lean closure repairs — 2026-11-21

## Scope and status

This is an intermediate source-integration and proof-repair record, not a completed TM63 root proof or a BB(6) result. The target was `TM63GeneralQ4TerminalComposition.lean` under Lean 4.36.0-rc2.

## Directly compiled modules

The following eight modules were repaired and individually compiled locally. Their emitted `#print axioms` reports contained no `sorryAx`:

- `im-results/agent24-champion-time/CountedLBinDecHRun.lean`
- `im-results/agent48-counted-inc0/M0EvenEightValuationMacros.lean`
- `im-results/agent44-tm63-middle/SectionResultRunSource.lean`
- `im-results/agent44-tm63-middle/GeneralQ4TailArithmetic.lean`
- `im-results/agent48-counted-inc0/M0EvenEightValuationSweepFacts.lean`
- `im-results/agent48-counted-inc0/M0EvenFourQ4Bridge.lean`
- `im-results/agent48-counted-inc0/PositiveZSecondCycleBridge.lean`
- `im-results/agent48-counted-inc0/PositiveZFirstCycleBridges.lean`

Key fixes:
1. Corrected induction-hypothesis applications where the tape coordinate was fixed by induction and therefore was not an IH argument.
2. Made Nat subtraction occur before coercion to Int in sweep-coordinate identities.
3. Supplied normalized disequalities to simplification in exact tape-update proofs.
4. Imported `CountedReset` and opened its namespace in `SectionResultRunSource` for the actual `run_add` lemma.
5. Replaced unavailable Mathlib-only constructs with Lean-core alternatives (`Nat.strongRecOn`, `Nat.mul_lt_mul_of_pos_left`, explicit power positivity and finite arithmetic).
6. Corrected the exact ordered-list representation of finite configurations. Direct `fRun` evaluation confirmed that the 22-step and 34-step runs reached the expected state and head with the same written cells, but in a different list order. The 51-step M0 bridge had the same representation issue.

Five direct/transitive importers used `import Agent6Q4Prefix`, although the source module is `CountedQ4Prefix.lean` and retains namespace `BB6Coverage.Agent6Q4Prefix`. Those imports were changed to `CountedQ4Prefix`.

## Remaining blockers

The full root import closure was not compiled. The closure contains about 192 Lean modules; further transitive source failures remain, notably in `M1EvenValuationBridge.lean`, `CountedResetBase`, and additional valuation/sweep modules. The attempted local M1 edits were not included in the patch. No claim is made here that `TM63GeneralQ4TerminalComposition` compiles, that its transitive axiom profile is clean, or that the full TM63 blank-start run has been proved.

## Reproduction details

Lean 4.36.0-rc2 was reconstructed from the uploaded split archive. The source-closure runner needs the explicit override:

```sh
python3 tools/lean_compile_closure.py \
  im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean \
  --workdir /tmp/tm63-closure \
  --jobs 8 \
  --override TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean
```

For the terminal source, extract `TerminalProofs.tar.xz.b64` first, then decode `TerminalLeftExact.lean.xz.b64` over `TerminalLeft.lean`; reversing that order overwrites the exact left proof with the older archived checkpoint.


## Additional reset-base repair

`im-results/agent8-counted-reset/CountedResetBase.lean` now parses and compiles. The misplaced module documentation comment and consecutive declaration-documentation comments were converted to ordinary block comments; the base valuation fact now uses `v2_of_odd`. The 63/67/71-step finite traces and all-head checks use `native_decide`, which compiles and reports no `sorryAx`, but introduces generated `native_decide` constants in the axiom report. Treat these as native-computation certificates, not as plain kernel-reduction proofs, and retain that distinction in any final formal audit.
