# Source-accepted Canonical41 five-parent reduction

The accepted Canonical46 ready-parent interface can be reduced by five further, pairwise distinct parent Covers: Raw63, Raw61, Raw67, Raw59 and Raw122. The resulting quotient roster has **41 retained representatives**.

This is a conditional global interface, not a proof of the BB(6) upper bound. Its fixed-score theorem says that if all 41 retained representatives satisfy a Cover at the already source-certified champion score, then that score is exactly BB(6).

## Accepted composition

GitHub Actions run [46037391095](https://github.com/FlareZ123/bb6/actions/runs/46037391095), at revision `d8b2c451bfa272f64e510fc9d80fcf0f5efe3ea2`, source-accepted the five removals in sequence:

| Parent | Literal table | Imported weighted bound | Accepted producer run |
|---|---|---:|---:|
| Raw63 | `1RB---_1RC1LA_0RD---_1LD1RE_---0LB_------` | 358 | 45948590270 |
| Raw61 | `1RB---_1RC0LA_0RD---_1LD1RE_---0LB_------` | 1,962 | 46032302566 |
| Raw67 | `1RB---_1RC1LB_0RD---_1LD1RE_---0LB_------` | 808 | 46034483043 |
| Raw59 | accepted staged parent closure | 4,136,171 exact local threshold | 45897242410 |
| Raw122 | `1RB---_1RC---_0RD---_1LD1RE_---0LF_------` | 6,659,487 | 45866162212 |

All five bounds are below the common reduction threshold 6,766,859. The consumer checked unique membership/removal success through the finite quotient roster and ended at

```lean
BB6.Agent31Canonical41Extra63R61R67R59R122.exact_at_champion_score
```

whose reported axiom profile is only `[propext, Classical.choice, Quot.sound]`. The successive accepted log states were 45, 44, 43, 42 and finally **41 retained**.

The run exported `canonical-extra-ready-thin-delta`, artifact **15221387172**, ZIP SHA-256
`5c95aa1c657a36dea9958216e16f5b5b2c731de262d45a0a2cd42ba088d59697`.

## Mathematical scope

The theorem composes the accepted Canonical46 soundness theorem with five actual parent Covers. Therefore every total machine compatible with the normalized root is either already bounded at the common threshold or is quotient-compatible with one of the 41 retained representatives. At the exact published champion score, the same reduction is connected to the source-certified blank-start champion witness.

The result does **not** assert that the 41 hypotheses are discharged. Exact BB(6) remains open until every retained representative is covered at the champion score (or an equivalent exhaustive universal argument is proved).

This reduction supersedes Canonical46 as the strongest source-accepted conditional weighted-TNF interface currently represented in the repository.
