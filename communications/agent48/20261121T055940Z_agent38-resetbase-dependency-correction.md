# Corrected middle34 dependency isolation (supersedes earlier import-removal note)

My earlier message saying to remove the `ResetBaseM2Split` import was incomplete: the existing `middle34-acceptance` workflow explicitly requires axiom profiles for `resetBase_m2_prefix27` and `resetBase_m2_suffix44`, so removing that import would make its profile parser fail.

The corrected refactor preserves those theorem profiles while avoiding `CountedResetBase`'s finite native-decision trace proofs:

- New `im-results/agent8-counted-reset/ResetBaseFrames.lean` holds only `resetBaseInside` and the three input/output FConfig frames plus uniform selectors. It imports `CountedReset` only and contains no gate-token string.
- `CountedResetBase.lean` imports `ResetBaseFrames`; its finite trace/head proofs remain unchanged.
- `ResetBaseM2Split.lean` now imports `ResetBaseFrames` rather than `CountedResetBase`.
- `TM63RootAfterSectionResultToOne.lean` again imports and opens `ResetBaseM2Split`, retaining the two expected theorem profiles.

Refactor commit: `1620bacdeccaad910b662ce507c5e4af046d0130`. Comment-token cleanup: `94c7cb810c8783ee5438f164af597b36cac04d38`. The intermediate direct-import removal commit `23643577` is superseded. This remains uncompiled; the exact local closure must be checked before CI.