# Raw140 exact residual frontier and Canonical48 integration

Agent15, 2026-11-28. **Intermediate until the current pinned-source audit succeeds.**

## Parent and exact source-cut remainder

Raw140 parent:

```text
1RB---_1RC0LD_1RD0RA_1LB1LE_0LB0RE_------
```

The existing source-backed three-hole cut has 89 leaves. Its accepted decomposition
has 54 FAR leaves, 23 leaves discharged by independent proofs, and exactly 12
unresolved one-hole cylinders. This run strengthens the generated Lean object
from a count-only statement to an exact residual identity using the injective
`BB6.Agent50FastKey.tableCode`.

| id | residual table | tableCode |
|---:|---|---:|
| 31 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LD---` | 93545900638368549 |
| 35 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RC---` | 93122399351408421 |
| 37 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RE---` | 94251736116635429 |
| 40 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1LC---` | 93263566447061797 |
| 41 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1LE---` | 94392903212288805 |
| 43 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RB---` | 92840065160101669 |
| 44 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RC---` | 93404733542715173 |
| 45 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RD---` | 93969401925328677 |
| 46 | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RE---` | 94534070307942181 |
| 74 | `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LC---` | 92981232255755097 |
| 83 | `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1LE---` | 94392903212288857 |
| 85 | `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RB---` | 92840065160101721 |

Generated module `BB6.Agent10Raw140ThreeHole` now exports:

- `remaining_count : remaining.length = 12`;
- `remaining_exact : remainingCodes = expectedCodes`;
- `remaining_nodup : remainingCodes.Nodup`;
- `sound`, the ordinary compatibility cut;
- `quotient_sound`, the same exact residual cut lifted through TNF state
  renaming with the existing `BB6.Agent50PartialPrefix.partialQuotientSound`;
- `cover`, the existing whole-parent consumer conditional on all residual Covers.

The exact-key theorem is materially stronger than the old count-only interface:
downstream consumers can refer to a stable mathematical residual roster rather
than artifact order or JSON positions.

## Global post-Raw47 integration

`Raw140Canonical48.lean` starts from
`BB6.Agent9Raw47AfterRaw112Conditional.roster37`, where Raw140 occurs exactly
once after the Raw39 -> Raw112 -> Raw47 lineage. It replaces that one parent
with the exact twelve Raw140 residual entries using
`BB6.Agent50QuotientRefinement.refineRoster`.

The intended checked shape is therefore

```text
37 canonical parents
- 1 Raw140 parent
+ 12 exact Raw140 residuals
= 48 global obligations.
```

Key theorems:

- `p140_count37`: Raw140 occurs exactly once in the Canonical37 roster;
- `count48`: the refined roster has exactly 48 entries;
- `raw140_parent_removed`: the unreﬁned Raw140 parent no longer occurs;
- `refined_sound_at`: the global first-one soundness theorem now returns one
  of the 48 refined TNF-quotient cylinders;
- `conditional_exact_at_champion_score`: given the already-authenticated
  Raw47 whole-parent Cover and Covers for the single 48-entry refined roster,
  derive `ExactBB6 (proposedTM63Moves + 7)`.

This removes the split interface that separately required twelve Raw140 residual
Cover assumptions plus 36 other canonical Covers.

## Raw37 structural work

Residual 37 has a source-accepted blank entry and common section theorem. This
run is converting its long hard return into reusable symbolic pieces under
`im-results/agent15-raw140-hard-prefix/`.

A reproducible block simulator, `analyze_raw37.py`, checks:

- `transferOut -> S(2,134,410,1)` in exactly 505,387 block exits and
  1,454,281 primitive steps;
- an affine middle phase `K_m -> K_(m+1)` for every `m=0..25`, with block
  cost `3663+432m` and primitive cost `10075+1188m`;
- the aggregate `K_0 -> K_26` cost: 235,638 block exits and 648,050
  primitive steps.

The shared `Raw14037RootBridge` also had a proof-shape gap that caused
`transfer_run` / `afterBank_to_transferOut` to carry `sorryAx`.
Commits `818aea4c...` and `8ea66eab...` normalize the transfer input and
unfold `BState.prim`; fresh CI is pending.

## Verification status

The authoritative unified pinned-source gate is workflow input
`raw140-canonical48`, run **46166732845**. It reconstructs the original
source-backed Raw140 dependencies, regenerates `Raw140ThreeHoleCut.lean`,
audits `remaining_exact`, `remaining_nodup`, `quotient_sound`, and then
compiles/audits `Raw140Canonical48.lean`.

Until that run succeeds, the new exact/global theorems above remain pending
verification and are intentionally kept in `im-results/`, not `results/`.
