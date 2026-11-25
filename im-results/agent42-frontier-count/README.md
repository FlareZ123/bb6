# Structural counts for first-hole frontiers

This directory contains reusable Lean lemmas intended to replace large `by decide` count proofs over proof-carrying frontier trees and quotient rosters.

## Rooted frontier counts

`RootedFrontierCount.lean` defines a pure path projection `pureResiduals` and proves:

- `residuals_buildFrontierB`: the executable residual list of `buildFrontierB` is exactly the pure path projection;
- `pureResiduals_length`: every path edge contributes exactly 23 off-path ordinary children;
- `residuals_length_buildFrontierB`: a path of length (n) has exactly (23n) retained ordinary residuals.

The proof is structural: it uses the finite 24-move roster, its nodup/completeness facts, and a pointwise flatMap congruence. It does not evaluate the full dependent frontier.

## Graft roster counts

`GraftRosterCount.lean` defines `graftMatchCount` and proves:

[
|operatorname{graftRoster}(p,R,S)| + m
= |S| + m|R|,
]

where (m) is the number of matching parent entries. In the one-parent case:

[
|operatorname{graftRoster}(p,R,S)| + 1 = |S| + |R|.
]

This additive identity avoids nonlinear subtraction and evaluation of a large function-valued roster. The same file also provides `replaceList_length_add_count` and `replaceList_length_of_one` for exact-equality replacements such as Agent48's packed-table `replacePacked`.

## Validation

These lemmas are intermediate until the `weighted-tnf-agent42-frontier-count` target in `.github/workflows/agent13-coverage.yml` completes successfully and the emitted axiom reports are checked. The D3 raw13 integration and Agent48 A6 count replacement should not assume acceptance before then.
