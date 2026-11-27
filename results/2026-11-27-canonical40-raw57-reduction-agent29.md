# Source-accepted Canonical40: remove Raw57 from the Canonical41 BB(6) quotient frontier

**27 November 2026 — an unconditional local parent elimination and a stronger conditional global interface. The exact value BB(6) remains open.**

## Main theorem

The existing formally accepted weighted first-one/quotient classifier reduced the universal six-state, two-symbol blank-start problem to the **41** canonical residual parent hypotheses in `BB6.Agent31Canonical41Extra63R61R67R59R122.exact_at_champion_score`. The complete six-hole Raw57 parent

```
1RB---_1RC---_0RD---_1LD1RE_---0LA_------
```

is now source-accepted at `WeightedBound 1613`; see [the separately certified Raw57 Cover](2026-11-27-raw57-complete-six-hole-cover-agent29.md). The source-accepted successor **removes that exact partial machine from the Canonical41 roster**, leaving 40 residual hypotheses.

The final Lean interface is

```lean
BB6.Agent31Canonical40Extra57.exact_at_champion_score
```

in the generated module `Canonical40Extra57.lean`. It proves the conditional statement that the named machine is a Busy Beaver maximizer at its exact source-certified score, **provided that every remaining representative in `roster40` admits the weighted-Bound Cover at the same target**. The crucial exported subsidiary assertions are:

```lean
p57_count41       -- Raw57 appears exactly once in the accepted 41-entry roster
p57_cover         -- its full Cover is transported to the common global threshold
parents_pairwise_distinct
count40           -- the retained quotient roster contains exactly 40 entries
all_ready_parents_removed
sound_integrated  -- every original-compatible machine is bounded or belongs to roster40
exact_at_target
exact_at_champion_score
```

There are **no assumptions about Raw57 itself** left in the final frontier: its all-completion boundedness was discharged in the independently accepted source. Likewise, this is not merely subtracting one from a stated count; the exact roster identity, complement cardinality and soundness are checked by Lean.

## Evidence and reproducible integration

| Check | Source-accepted evidence |
| --- | --- |
| Canonical41 predecessor | [CI 46037391095](https://github.com/FlareZ123/bb6/actions/runs/46037391095), artifact 15221387172 |
| Raw57 complete parent Cover | [CI 46074414244](https://github.com/FlareZ123/bb6/actions/runs/46074414244), artifact 15234538009 |
| **Canonical41 → Canonical40 successor** | **[CI 46075158700](https://github.com/FlareZ123/bb6/actions/runs/46075158700), success** |
| Accepted thin delta artifact | [15234886499](https://github.com/FlareZ123/bb6/actions/runs/46075158700/artifacts/15234886499), `canonical40-raw57-thin-delta` |
| Delta zip SHA-256 | `d1547d32ca4668d250978f288c827287cadd425eef9c8e0c230802d313177207` |
| Root object | `Canonical40Extra57.olean` |
| Root object SHA-256 | `fb778a843933cfe5fd0fae4903804b5f848a0e5b833f207cd4cb3ac018430175` |
| Source commit used for workflow | `6837dc674c940cb4d9034b9b966811d495139be0` |
| Final reported residuals | **40** |
| Logical axiom boundary | The consumer enforces only `propext`, `Classical.choice`, and `Quot.sound`; nonstandard axioms or a missing expected theorem cause rejection |

The reusable source consumer is `im-results/agent29-raw57-consumer/consume_after_canonical41.py` and its manual runner is `.github/workflows/agent29-canonical40-raw57.yml`. It authenticates the pinned Canonical41 predecessor, verifies the entire original-source Raw57 parent manifest and object identities, compiles the concrete membership and removal proof, and retains only the new delta objects. Its final success output is `status: source-accepted Raw57 successor of Canonical41`, `remaining_residual_count: 40`. In particular, the global quotient proof does not rely on a mere verbal claim that Raw57 was present.

The Raw57 local bound 1613 is far below the common global weighted threshold 6,766,859; the consumer proves the monotone lifting within the soundness chain before removing the parent.

## What is not decided

The theorem **does not establish a universal upper bound** for all six-state machines. Forty residual quotient Covers still remain unproved at the champion score, including difficult arithmetic/counter families and cryptids. It is also not an extra unit of reduction for every independently generated Canonical41→40 delta: distinct parent removals must be composed and checked in the *same* successor roster before claiming 39.

The current source-accepted frontier is therefore **Canonical40**, improving the prior Canonical41 by one fully discharged parent while preserving the exact named champion witness and the conditional maximizer theorem.
