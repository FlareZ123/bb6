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

For every `b,d : Nat` with `d ≥ 2b+6`, the source-level high-level
transition is

```
C(b,d)  ↦  C(2b+4, d-2b-6).
```

**Derivation.** In this region, `d-b ≥ b+6 ≥ 6`. Thus the `C(b,d)`
dispatcher takes its generic `C(b, t+2)` case with `t=d-2`; it does not
take the `b ≥ t+1`, `t=b`, `t=b+1`, or `t=b+2` branches. The generic
branch is exactly
`drainA (3b+3) 2 (d-b-5)`. Its third argument is at least `b+1`, while
`(3b+3)/3=b+1`; hence the first `drainA` step chooses
`k=b+1`. The resulting first counter is zero, the second is
`2+2(b+1)=2b+4`, and the third is
`(d-b-5)-(b+1)=d-2b-6`. This is the displayed transition.

Consequently, for any consecutive run of `k` such transitions beginning at
`C(b₀,d₀)`, the exact state is

```
b_k = 2^k (b₀+4) - 4
d_k = d₀ - 2 (b₀+4) (2^k - 1) + 2k.
```

This follows by induction from the two affine recurrences above. The run
continues while the current state remains in the region
`d_k ≥ 2b_k+6`.

The halting target on this ray is therefore equivalent to

```
d_k = b_k + 2
iff
d₀ = 3 (b₀+4) 2^k - 2b₀ - 10 - 2k.
```

For the important `b₀=1` ray, the only possible starting values that halt
during the ray are

```
d₀ = 15 · 2^k - 12 - 2k.
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
doubling-ray lemma gives `C(6,9)`; the ray then exits because
`9 < 2·6+6`. Its only halting candidates are `3,16,44,102,…`,
so `17` is not a candidate.

The next exact dispatcher calls are

```
C(6,9)  ↦ drainA(20,0,6)  = C(2,25)
C(2,25) ↦ drainA(9,2,18)  = C(8,15)
C(8,15) ↦ drainA(27,2,2)  = C(1,57).
```

For example, the first drain has reductions
`(20,0,6) → (2,12,0) → (0,2,25)`. The second has
`(9,2,18) → (0,8,15)`. The third has
`(27,2,2) → (21,6,0) → (1,14,7) → C(1,57)`.

The next `b₀=1` ray begins at `C(1,57)` and has two doubling steps:
`C(1,57) → C(6,49) → C(16,31)`. Since `57` is odd and at least
five, the ray formula excludes a hit of `C(b,b+2)` throughout this segment.
The next generic drain is
`drainA(51,2,10) = C(1,185)`, with reductions
`(51,2,10) → (21,22,0) → (1,14,39) → C(1,185)`.

## What remains open

The result controls only the exact doubling region. When a ray exits
`d ≥ 2b+6`, the high-level dispatcher may enter the other `drainA`
branches (including the `b ≥ d-1` branch). Those cascade states are not
covered by the ray formula, and no invariant has been proved here to show
that they avoid `C(b,b+2)`.

Therefore this is **not** a proof of non-halting, not a full orbit
classification, and not a BB(6) result. The next meaningful mathematical
step would be an exact return map for the exceptional cascade branches,
including a proof that no intermediate section state is `C(b,b+2)`.
