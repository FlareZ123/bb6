# Odd-Rst2 q4 prefix

## Status

The Lean source is in `CountedQ4Prefix.lean`. The theorem is a parameter-uniform source-run statement for the actual TM63 transition table. It is an intermediate bridge result, so it belongs in `im-results/`, not the academically publishable `results/` index.

The isolated dependency chain is only `ChampionRootBridge`, `CountedSweep`, and `S1Encoder`. The proof intentionally does not import the currently failing `CountedResetBase` or the q4 suffix module. Its local definitions of `q4LeftFacing` and `q4RightShape` are textually identical to the definitions in Agent 8's `Q4Suffix.lean`.

Kernel status: the first CI attempt stopped before this module because of pre-existing errors in `CountedResetBase.lean`. The champion-root workflow has since been moved to compile this module immediately after `S1Encoder`; the next run is the relevant proof check. Until that output is inspected, treat the Lean proof as an unverified candidate.

## Theorem interface

`BB6Coverage.Agent6Q4Prefix.oddRst2_q4_prefix` states, for odd `n` with `n < 2^L`, arbitrary `a,b`, and arbitrary absolute head `h`, that the original source configuration

```lean
s1Config L n 2 a 0 b h
```

reaches state E (state index 4) at the same head after exactly `32 + 12*a` transitions. The resulting tape satisfies:

- the head cell is marked;
- its complete left-facing stream is `q4LeftFacing L (n-1) a`;
- its right half satisfies `q4RightShape Tq h b`.

The q4 definitions are local to this module to keep the prefix theorem independent of Agent 8's suffix module. Their definitions match Agent 8's interface exactly.

## Proof decomposition

Let `N = 3*a+2`.

1. The S1 left-facing source begins with `d1pow a ++ markerWord 2`, giving exactly `N` consecutive ones at and to the left of the head. The cell immediately to the right is blank.
2. `counted_left_sweep` shifts those `N` ones one cell right and moves left by `N`, costing `3*N = 9*a+6`.
3. At the translated head, the eight-cell local bridge window `[-6,1]` agrees with finite start `FConfig 3 0 [-4,-1]`. The fixed 26-step trace ends at state E, relative head 2, with marked cells `[1,-1,-4,-5,-6]`.
4. The shifted run contains `3*a` consecutive ones immediately to the right of the new state-E head. `E_scan` consumes exactly these in `3*a` steps and returns the head to its original coordinate.

Thus the prefix cost is

```
3*(3*a+2) + 26 + 3*a = 32 + 12*a.
```

The bridge output in left-facing order is `1,0,1,0,0,1,1,1`: marker-1, d0 delimiter, and the first d1 block of `binDec L (n-1)`. For odd n, the source counter begins `d0 ++ tail`, while its predecessor begins `d1 ++ tail`; the bridge changes the first two counter bits and the source already supplies the common third bit. Cells beyond the local frame are preserved, establishing the complete left-facing identity rather than only a finite prefix.

The right-hand q4 word is `1^5 00 1^(3*(b+1)) 0^∞`, with the head on its first one. This is precisely the shape consumed by Agent 8's q4 suffix theorem.
