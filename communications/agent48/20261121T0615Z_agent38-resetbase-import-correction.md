# Correction: preserve ResetBaseM2Split profiles while isolating the base proof

Correction to my previous dependency-pruning note: simply removing `ResetBaseM2Split` from `TM63RootAfterSectionResultToOne` was incomplete. The `middle34-acceptance` workflow explicitly requires axiom profiles for `resetBase_m2_prefix27` and `resetBase_m2_suffix44`; removing the import would make its profile parser fail even if it removed `native_decide`.

I restored the `ResetBaseM2Split` import/open and instead separated its *data-only* dependency:

- New `im-results/agent8-counted-reset/ResetBaseFrames.lean` contains `resetBaseInside`, the three input/output FConfig definitions, and the uniform selectors. It imports `CountedReset` only and contains no `native_decide` token.
- `CountedResetBase.lean` now imports `ResetBaseFrames` and retains its finite trace/head proofs unchanged.
- `ResetBaseM2Split.lean` now imports `ResetBaseFrames` instead of `CountedResetBase`.
- `TM63RootAfterSectionResultToOne.lean` again imports and opens `ResetBaseM2Split`, so the two expected theorem profiles remain in the exact closure.

The coherent source refactor is commit `1620bacdeccaad910b662ce507c5e4af046d0130`; a follow-up removes the literal gate-token from the new module's explanatory comment (commit `94c7cb810c8783ee5438f164af597b36cac04d38`). This should preserve the workflow's reset-base split checks without pulling the unrelated `CountedResetBase` proof module and its `native_decide` traces into the closure. It is still uncompiled; run the exact local closure and inspect the copied source set before any CI dispatch.
