# D-root total-replay orbit probe (100,000 returns)

This is an intermediate computational probe, not a proof of halting or nonhalting. It uses an independent JavaScript/BigInt port of the repository's source evaluator at `im-results/agent3-d-density-drift/evaluator.py`.

Run from the repository root:

```sh
node im-results/agent50-d-root-100k/run.js 100000
```

## Observed result

For each of the four authentic empty-suffix roots (9, 5, 15, 39), the exact total-return evaluator completed 100,000 iterations without returning terminal.

| Root | Residue counts (0,1,2) | Distinct suffixes visited | Maximum suffix length | Empty suffix visits | Final suffix |
|---:|---:|---:|---:|---:|---|
| 9 | 33,227 / 33,378 / 33,395 | 93 | 26 | 61,002 | `0111111` |
| 5 | 33,148 / 33,529 / 33,323 | 97 | 27 | 60,763 | empty |
| 15 | 33,250 / 33,357 / 33,393 | 93 | 28 | 60,993 | empty |
| 39 | 33,527 / 33,239 / 33,234 | 93 | 27 | 61,090 | `0111111` |

The final unary parameters have 141,507–141,510 ternary-independent binary bits (reported as bit length by the script).

The first checkpoints agree with the existing source anchors:
- Root 9 after 10 returns: (n=196699), empty suffix.
- Root 5 after 10 returns: (n=123501), suffix `0111111`.
- Root 15 after 10 returns: (n=276715), empty suffix.
- Root 39 after 9 returns: (n=277451), empty suffix.

## Interpretation and caveats

- This is exact finite simulation of the total recurrence; it does not establish all-time avoidance or eventual halting.
- The residue counts are close to one third each over this finite window. This is empirical only and must not be promoted to an equidistribution claim.
- Each root visits only 93–97 exact suffix strings in this window, but the unrestricted suffix-only transition closure from the empty suffix exceeded 100,000 states in a separate breadth-first probe. Thus the observed root suffix sets are not, by themselves, a closed finite automaton.
- The useful next question is whether the correlated root orbit admits a source-level invariant or a finite *joint* abstraction involving both the suffix and the evolving 3-adic residue stream. Do not infer a finite-state suffix system from this probe.

The existing D-root phase-separation and density-one results remain the mathematical basis; this file records only a reproducible finite experiment.
