# Exact doubling rays in the #153 high-level map

**Status:** intermediate exact reduction only. This does not prove that the machine is non-halting and does not change its cryptid status.

## Source and section map

The machine is
`1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`
(upstream BB(6) index #153). The exact source used here is the pinned
[Google DeepMind `cryptids` source at commit `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean).
Its `HighLevelState.C b d` section map has the halting target `C(b,b+2)`.
The upstream hardness catalogue calls this a single-base exponential cascade,
with a two-base `2^n`/ `4^n` growth pattern, no identified shield, and an
open cryptid status. The local repository's upstream-coverage ledger records
this exact machine; there was no separate local derivation of the ray formula
below.

## Exact doubling-ray lemma

For every `b ≥ 1` and `d ≥ 2b+4`, the source-level high-level transition is

```
C(b,d)  ↦  C(2b+4, d-2b-4).
```

**Derivation.** In this region, `d-b ≥ b+4 ≥ 5`. Thus the `C(b,d)`
dispatcher does not take its `d=b+2`, `d=b+3`, or `d=b+4` cases, and
`b ≥ d-1` is false. It takes the generic branch
`drainA (3b+3) 2 (d-b-3)`. In the first `drainA` step, the third argument
is at least `b+1`, while `(3b+3)/3=b+1`; hence the chosen decrement is
exactly `k=b+1`. The resulting first counter is zero, the second is
`2+2(b+1)=2b+4`, and the third is
`(d-b-3)-(b+1)=d-2b-4`. This is the displayed transition.

Consequently, for any consecutive run of `k` such transitions beginning at
`C(b₀,d₀)`, the exact state is

```
b_k = 2^k (b₀+4) - 4
d_k = d₀ - 2 (b₀+4) (2^k - 1) + 4k.
```

This follows by induction from the two affine recurrences above. The run
continues precisely while the current state remains in the region
`d_k ≥ 2b_k+4`.

The halting target on this ray is therefore equivalent to

```
d_k = b_k + 2
iff
d₀ = 3 (b₀+4) 2^k - 2b₀ - 10 - 4k.
```

For the important `b₀=1` ray, the only possible starting values that halt
during the ray are

```
d₀ = 15 · 2^k - 12 - 4k.
```

In particular, an odd start `C(1,D)` with `D ≥ 5` cannot halt on its
doubling ray: for `k ≥ 1` the displayed candidate is even, while for
`k=0` it is `3`.

## Exact root prefix

The pinned source gives the initial section transitions

```
C(0,0) ↦ C(0,4) ↦ C(1,17).
```

The first arrow is the `d=0` case. For the second, the `d=b+4` case
reduces to `drainA 4 0 4 = C(1,17)`. Starting from `C(1,17)`, the
doubling-ray lemma gives `C(6,11)`; the ray then exits because
`11 < 2·6+4`. Its only halting candidates are `3,14,40,96,…`,
so `17` is not a candidate.

The next exact dispatcher call is

```
C(6,11) ↦ drainA(21,2,2) = C(1,57).
```

For the drain equality, the successive source reductions are
`(21,2,2) → (15,6,0) → (1,10,9) → C(1,57)`.
Thus the root has reached a second odd `b₀=1` ray. The formula proves that
this ray also cannot hit the halting target while it stays in the doubling
region.

## What remains open

The result controls only the exact doubling region. When a ray exits
`d ≥ 2b+4`, the high-level dispatcher may enter the other `drainA`
branches (including the `b ≥ d-1` branch). Those cascade states are not
covered by the ray formula, and no invariant has been proved here to show
that they avoid `C(b,b+2)`.

Therefore this is **not** a proof of non-halting, not a full orbit
classification, and not a BB(6) result. The next meaningful mathematical
step would be an exact return map for the exceptional cascade branches,
including a proof that no intermediate section state is `C(b,b+2)`.
