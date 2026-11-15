# TM63 left-counter increment: exact H-run factorization

<badge label="Intermediate proof derivation — not Lean-checked" color="warning" />

## Source theorem being implemented

In the original `verify/SOBCv5.v`, module `TM63`, the left-counter decrement is reduced to `BinaryCounter_v2.LBinDec_spec`. The one-block hypothesis required by `LBinDec_spec` is:

```coq
forall l r n,
  l <* d0 <* d1^^n <{{D}} [0] *> r -->+
  l <* d1 <* d0^^n <* [1] {{B}}> r
```

Here `d0 = <[1;0;0]` has head-facing stream order `[0,0,1]`, and `d1=[1,1,1]`. The `<*` notation prepends the indicated list to the head-facing left stream. The original transition table is the repository's `tm2`:
`1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`.

## Exact run decomposition

For a left stream `d1^n ++ d0 ++ l`, a right stream `[0] ++ r`, and state D at head position `h`, the H-run is exactly `12*n+4` successful transitions:

1. **Left sweep: `9*n` steps.** Apply the existing `counted_left_sweep` for `3*n` one-cells. Its input is `leftOnes T h (3*n)` and `T(h+1)=false`. The head reaches `h' = h-3*n` in state D. The shifted block of `3*n` ones now occupies `[h'+2,h+1]`. The cells `h'-1,h',h'+1` are all zero: the first two are the first two cells of the original `d0`, and the third is the zero shifted left from `h+1`.

2. **Four-cell bridge: 4 steps.** Starting in D at `h'`, with zeros at `h'-1,h',h'+1`:
   - D0 writes 0 and moves left to C at `h'-1`;
   - C0 writes 1 and moves right to E at `h'`;
   - E0 writes 1 and moves right to A at `h'+1`;
   - A0 writes 1 and moves right to B at `h'+2`.

   Thus the bridge writes 1 at `h'-1,h',h'+1`, leaves the shifted block `[h'+2,h+1]` untouched, and ends in B at `h'+2`.

3. **B/F/D right sweep: `3*n` steps.** Starting in B at `h'+2`, scan the `n` triples of ones in `[h'+2,h+1]`. Each triple is processed by B1 → F1 → D1 → B, writing `001` in increasing tape coordinates and advancing the head by three. The final head is `h'+2+3*n=h+2`, in state B.

The total is `9*n+4+3*n=12*n+4`.

## Missing reusable sweep lemmas

The existing `im-results/agent24-champion-time/CountedSweep.lean` proves the D/B/F right sweep, but not its cyclic B/F/D variant. The B-start variant has the same `rightOnes` predicate and the following exact one-triple update:

```lean
def afterRight3B (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h || x=h+1 then false else T x
```

With `T h=T(h+1)=T(h+2)=true`, the original machine runs

```lean
run tm2 3 ⟨1,h,T⟩ =
  some ⟨1,h+3,afterRight3B T h⟩
```

using the already available lookups `lookup11` (B1), `lookup51` (F1), and `lookup31` (D1). Define `sweptRightB` by iterating `afterRight3B` at offsets `h,h+3,…`; the induction proof of `counted_right_sweep_B` is the same as `counted_right_sweep`, with a `rightOnes_tail_B` lemma observing that the next triple begins at `h+3` and so avoids the two cells changed by `afterRight3B`.

The bridge is a separate direct four-step lemma from D at `h'`; it is not the existing `E_zero_bridge` (which starts in E). Its output update is:

```lean
def afterLIncBridge (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h-1 || x=h || x=h+1 then true else T x
```

## Sweep-to-sweep invariant

The key input to `counted_right_sweep_B` follows from the left sweep. For any `k`, the `k)-step `sweptLeft` shifts the original block of `k` ones one cell right:

```lean
sweptLeft k T h (h-(k:Int)+2+(i:Int)) = true
```

for every `i<k`, assuming `leftOnes T h k` and `T(h+1)=false`. Prove this by induction on k:
- the `i<k` case uses the existing `leftOnes_tail` lemma and the induction hypothesis at `h-1`;
- the final `i=k` cell is `h+1`, set to true by the first `holeThree` and preserved by `sweptLeft_preserves_right`.

Taking `k=3*n` and grouping indices `3*i,3*i+1,3*i+2` yields:

```lean
rightOnes (sweptLeft (3*n) T h) (h-(3*n:Int)+2) n
```

The four-step bridge changes only `h'-1,h',h'+1), strictly left of the B-sweep start `h'+2`, so this invariant survives the bridge.

## Final tape alignment

Let `h'=h-3*n`. After the B/F/D sweep:
- the final head is at `h+2` in state B;
- cell `h+1` is the separate leading `[1]` in the target left stream;
- the next `3*n` cells, read head-facing from `h) leftward, are `d0^n`: each `d0=[0,0,1]` block uses the first two zeroes written by one B/F/D triple and the final 1 from the preceding triple; the leftmost block takes its final 1 from the bridge's cell `h'+1`;
- cells `h',h'-1,h'-2` form `d1): the first two are bridge writes and the third is the original final 1 of the `d0` boundary block;
- the arbitrary left tail `l` below `h'-2` and right tail `r` beginning at the new head `h+2` are unchanged.

This is why the physical B/F/D output `001` is correctly aligned with the head-facing target `[1] ++ d0^n ++ d1 ++ l`: the bridge and the final sweep cell supply the one-cell offset. There is no orientation reversal.

## What this enables

Once the H-run theorem is proved with the exact `12*n+4` count and arbitrary contexts, it supplies the premise of the original `LBinDec_spec`. That shift-rule induction is the route to a single counted left-binary-decrement theorem, avoiding a catalogue of separately proved residue classes. The remaining work is to formalize the arbitrary-context tape equality and then lift the H-run through the binary-counter carry structure.

**Status:** the phase lengths, primitive transition sequence, sweep invariant, and final tape alignment are derived from the original TM63 transition table and the existing `CountedSweep` definitions. No new Lean theorem has been compiled in this invocation. This file is an `im-results/` research note, not a publishable result.


## Expected exact count for the generic LC decrement

The original Coq proof identifies the exact carry length. In `verify/BinaryCounter_v2.v`, `BinDec d0 d1 len n` is `BinaryCounter (2^(len+1)-1-n)`; `LBinDec_spec` delegates to `BinaryCounter.v:not_full_Inc`, which factors a non-full counter as

```coq
BinaryCounter c     = d1^^i *> d0 *> s
BinaryCounter (c+1) = d0^^i *> d1 *> s.
```

For the decrement `LC (n+1) → LC n`, the input counter is
`c = 2^(len+1)-1-(n+1)`, the bitwise complement (at the fixed width) of `n+1`. Its trailing-one count `i` is therefore exactly `v2(n+1)`, the trailing-zero count of the decremented source index. The H-run above costs `12*i+4`. Thus the expected exact counted LC theorem is:

```lean
run tm2 (12 * v2 (n+1) + 4)
  (LCInput len (n+1) l r) =
  some (LCOutput len n l r)
```

under `n+1 < 2^len`, with the actual configuration wrappers fixing state D / right boundary 0 and state B / left boundary 1. This is the source of the `4 + 12*v2(n)` contribution in the repository's `resetPrefixCost` formula. The remaining formal work is to expose the carry-length decomposition in Lean and compose the arbitrary-context H-run with it; the count should not be guessed from finite simulations.
