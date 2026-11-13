# Odd-Rst2 q4 prefix

## Status

`CountedQ4Prefix.lean` gives a parameter-uniform source-run theorem for the original TM63 transition table. It is an intermediate bridge result and belongs in `im-results/`, not the academically publishable `results/` index.

The core prefix theorem with its original finite right-shape interface passed the q4-prefix gate in Lean 4.36.0-rc2, CI run `43334058991`; its axiom report was `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The current source revision strengthens that interface by exporting the complete right-facing stream already proved internally. That strengthening was committed in `7369e2778204ed876a9cb8529981ac1f09ad9796` and **has not yet been compiled in CI**. Do not transfer the older green status to the strengthened source until the manual audit is rerun.

The direct Lean dependencies are `CountedSweep`, `CountedOddBase`, and `S1Encoder`. The proof intentionally does not import the currently failing `CountedResetBase` or the q4 suffix module. Its local definitions of `q4LeftFacing`, `q4RightFacing`, and `q4RightShape` are compatible with Agent 8's suffix interface.

## Theorem interface

`BB6Coverage.Agent6Q4Prefix.oddRst2_q4_prefix` states, for odd `n) with `n < 2^L`, arbitrary `a,b), and arbitrary absolute head `h), that the original source configuration

```lean
s1Config L n 2 a 0 b h
```

reaches state E (state index 4) at the same head after exactly `32 + 12*a` transitions. The resulting tape satisfies all of:

- the head cell is marked;
- its complete left-facing stream is `q4LeftFacing L (n-1) a`;
- its finite local right contract is `q4RightShape Tq h b`;
- its complete right-facing stream is
  `∀ i, Tq (h+1+i) = sideBit (q4RightFacing b) i`.

The last conjunct is the new interface strengthening. The right word `q4RightFacing b` is `[true,true,true,true,false,false] ++ d1pow (b+1)`, of length `9+3*b`. Therefore every right cell beyond that finite word is blank. This supplies the infinite blank ray needed to identify the full q4 suffix endpoint, not merely its five-cell local guard.

The q4 definitions are local to this module so the prefix theorem remains independent of Agent 8's suffix module. Their list and tape conventions match the suffix interface.

## Proof decomposition

Let `N = 3*a+2`.

1. The S1 left-facing source begins with `d1pow a ++ markerWord 2`, giving exactly `N` consecutive ones at and to the left of the head. The cell immediately to the right is blank.
2. `counted_left_sweep` shifts those `N) ones one cell right and moves left by `N), costing `3*N = 9*a+6`.
3. At the translated head, the eight-cell local bridge window `[-6,1]` agrees with finite start `FConfig 3 0 [-4,-1]`. The fixed 26-step trace ends at state E, relative head 2, with marked cells `[1,-1,-4,-5,-6]`.
4. The shifted run contains `3*a) consecutive ones immediately to the right of the new state-E head. `E_scan` consumes exactly these in `3*a) steps and returns the head to its original coordinate.

Thus the prefix cost is

```
3*(3*a+2) + 26 + 3*a = 32 + 12*a.
```

The bridge output in left-facing order is `1,0,1,0,0,1,1,1`: marker-1, d0 delimiter, and the first d1 block of `binDec L (n-1)`. For odd n, the source counter begins `d0 ++ tail`, while its predecessor begins `d1 ++ tail`; the bridge changes the first two counter bits and the source already supplies the common third bit. Cells beyond the local frame are preserved, establishing the complete left-facing identity rather than only a finite prefix.

On the right, the proof already establishes the exact stream equality for every index. The finite `q4RightShape` is derived from that stronger fact and remains the contract consumed by Agent 8's suffix theorem.

## Research scope

For the authentic root parameters `(L,n,m,a,z,b)=(3,7,2,6,0,63)`, the q4 prefix takes 104 primitive transitions. This is only the first segment of the marker-2 Rst2 route. The suffix must still be proved to return the complete tape to
`s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`; the proposed total `71+12*a+3*b) remains conditional until the suffix endpoint and run composition are kernel-checked. No exact BB(6) score or universal six-state upper bound follows from this prefix alone.
