# Exact weighted maximum of the Raw83 four-hole parent cylinder

## Theorem

Let
```
P83 = 1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA
```
be the four-hole partial six-state, two-symbol machine. It has (25^4=390{,}625) literal total-machine completions.

The original-source Lean development proves
[
\forall m,\; \operatorname{compatible}(P83,m)\;\to\;\operatorname{WeightedBound}(514,m).
]
The bound is attained by a compatible completion that makes 513 ordinary transitions and then halts, with zero incoming blank-delay surcharge. Thus 514 is the exact weighted maximum over this parent cylinder. The exact threshold theorem is
[
(\forall m,\; \operatorname{compatible}(P83,m)\to\operatorname{WeightedBound}(B,m))
\iff 514\le B.
]

The source-accepted declarations are `BB6.Agent10Raw83.all_completions` and `BB6.Agent10Raw83.exact_bound`; the witness is `longest` with `longest_halts` and `longest_delays`.

## Proof and verification

The exhaustive source audit contains 228 splits, 3,717 side-cycle leaves, 1,471 last-hole leaves, and 57 FAR leaves (54 ordinary FAR and three width-one run-quotient block FAR). All 390,625 physical completions are covered. No delayed leaf or growth assumption is used.

Original-source Lean 4.36.0-rc2 CI [run 45755362807](https://github.com/FlareZ123/bb6/actions/runs/45755362807), at revision `8d8a3fcc59600146fb25eb70afc2f34a31c99cb3`, passed the exact-bound and standard-axiom gates. Artifact `raw83-parent-proof` is ID **15087730774**, SHA-256 `89ea0f6ae8f0da2d11f86c959b1d848d7c4ef44e933899bfc2654c7dc1a9a1a2`. The proof source and detailed audit are in [the retained dossier](../im-results/agent10-raw83/README.md).

## Scope and global membership

This is an exact result for one four-hole parent cylinder, not a universal BB(6) upper bound. A separate Lean preflight is checking whether this exact table occurs exactly once in the original Canonical64 roster and remains distinct after the five-parent Canonical59 cut: [run 45824051367](https://github.com/FlareZ123/bb6/actions/runs/45824051367). Until that membership preflight passes and the parent is composed into the shared quotient consumer, no additional global residual reduction is claimed.
