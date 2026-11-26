# Raw118 exact weighted maximum 756,496

The six-hole partial machine

`1RB---_1RC---_0RD---_1LD1RE_---0LE_------`

has exact weighted maximum **756,496** under the project's `WeightedBound` convention. The parent has (25^6 = 244,140,625) physical completions.

## Exact parent theorem

The original-source Lean theorem

`BB6.Agent1Raw118Complete.parent_cover : Cover (WeightedBound 756496) parent`

proves that every compatible completion is covered at weighted score at most 756,496. The companion theorem `parent_exact` proves sharpness: every universal weighted cover of this parent has bound at least 756,496.

The parent assembly accounts for 959 residual tables: 958 candidate certificates and the explicit final M2869 holdout. The generated consumer checks the literal table partition before consuming each certificate. The complete parent Cover and exactness theorem passed original-source compilation and the configured axiom audit under Lean 4.36.0-rc2 in [CI run 45812415227](https://github.com/FlareZ123/bb6/actions/runs/45812415227), artifact [15120592642](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15120592642). The proof sources and certificate composition are preserved in the [Raw118 dossier](../im-results/agent16-raw118/README.md), especially [Raw118Complete.lean](../im-results/agent16-raw118/Raw118Complete.lean) and [Raw118Sharp.lean](../im-results/agent16-raw118/Raw118Sharp.lean).

## Attaining completion

The completion

`1RB1LE_1RC---_0RD1RA_1LD1RE_0LF0LE_1RF0RC`

executes 756,495 ordinary transitions before its first undefined query, B1. Filling that query with halt gives the exact score 756,496, with zero incoming delay. The packed trace refinement and 6,803-instruction replay are part of the source-checked witness.

## Canonical64 membership

The exact parent table occurs exactly once in the 64-entry Canonical64 roster. The theorem `BB6.Agent16Raw118Canonical64Membership.p118_parent_count64` proves the sameTable-filter count is one. This membership-only source audit passed strict linking and the standard-axiom gate in [CI run 45845180631](https://github.com/FlareZ123/bb6/actions/runs/45845180631), artifact [15131232543](https://github.com/FlareZ123/bb6/actions/runs/45845180631/artifacts/15131232543).

The membership result does not remove Raw118 from any roster. It is ready for the repository's single coordinated parent consumer, but the global 64-residual Cover obligation remains open. This local theorem is not a universal BB(6) upper bound and does not determine BB(6).
