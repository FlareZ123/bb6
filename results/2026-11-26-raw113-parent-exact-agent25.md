# Exact weighted maximum of the Raw113 six-hole parent cylinder

## Theorem

Let
```
P113 = 1RB---_1RC---_0RD---_1LD1RE_---1RC_------
```
be the six-hole partial six-state, two-symbol machine. It has (25^6=244{,}140{,}625) literal total-machine completions.

The original-source Lean development proves that every compatible completion satisfies
[
\operatorname{WeightedBound}(2674).
]
A compatible completion attains the bound: it makes 2,673 ordinary transitions and then executes the halting query, with zero incoming blank-delay surcharge. Consequently, 2,674 is the exact weighted maximum over this parent cylinder. The exported threshold theorem states that the universal parent bound at threshold (T) holds if and only if (2674\le T), and the parent Cover is available for every (T\ge2674).

The source-accepted declarations are:
- `BB6.Agent25Raw113.all113`: every compatible completion is bounded by 2,674;
- `BB6.Agent25Raw113.attained113`: an attaining completion with 2,673 ordinary moves plus the halt tick;
- `BB6.Agent25Raw113.exact113`: exact threshold characterization;
- `BB6.Agent25Raw113.cover113`: the corresponding `Cover (WeightedBound T)` for every (T\ge2674).

## Proof and verification

The 24 first-move roots were partitioned into six disjoint groups of four. All six independent original-source shard jobs passed in [run 45789881574](https://github.com/FlareZ123/bb6/actions/runs/45789881574), pinned to source revision `5a41fcb3c0f3fd01801145e503893da1bbe67c76).

The parent composition passed in [run 45802897709](https://github.com/FlareZ123/bb6/actions/runs/45802897709), job `139850451638`, at source revision `e91b9703f6dd7657d16bb9d428181a657ad14fff`. It checked all six shard pins and original manifests, reused all 533 dependency-closed modules, and compiled the three new parent assembly modules (536 project modules total). The four exported theorem profiles were exactly `[propext, Classical.choice, Quot.sound]`; the source audit rejected `sorryAx` and `native_decide`.

The retained `raw113-parent-proof` artifact is ID **15108067526**, SHA-256 `7d3ac590a7b9e562e430a00148616dc37d3eb0304fd1b20e9e3cbd07c611f865`. The detailed reproduction dossier, including the generator and shard layout, is [here](../im-results/agent25-raw113/README.md).

## Scope

This is a complete exact result for one six-hole E1 parent cylinder, not a universal upper bound for BB(6). Raw113 is distinct from the published champion's Raw139 parent: Raw113 fixes (C0=0RD), whereas the champion's Raw139 fixes (C0=1LD). No champion-parent or global-roster claim is implied by this theorem; exact membership and consumption in the accepted Canonical64 interface are separate obligations.
