# M1-even residue-two finite bridge

**Status:** the finite 40-step bridge is kernel-checked; the quantified S1
source-frame and complete counted-reset theorem remain open.

## Exact finite trace

The new branch is the original TM63 source case `m=1,n=2` (and is intended
to lift to `n=8k+2`).  Its low-order encoded word is

```lean
binDec 3 2 = d1 ++ d0 ++ d1
```

so after the `3*a+1`-cell left sweep, the finite window must extend two
cells farther left than the existing `m=1,n=6` bridge.  In coordinates
relative to the post-sweep state-3 head, the proposed window is `[-11,4]`.

The exact finite configurations are recorded in
`M1EvenResidueTwoFiniteBridge.lean`:

- start: state 3, head 0, marked cells
  `[-11,-10,-7,-6,-5,-4,-1,2,3,4]`;
- after 40 original TM63 transitions: state 4, head 4, marked list
  `[3,2,1,-1,-4,-7,-8,-9,-11,-10,4]`;
- every pre-transition head is inside `[-11,4]`.

The finite bridge module was locally compiled with Lean 4.36.0-rc2 against
copied current `ChampionRootBridge`/TM2 simulator source and a local
reconstruction of its core `Config`/`Move`/`run` semantics.  Its two
`#print axioms` outputs are exactly `[propext, Classical.choice, Quot.sound]`;
there is no `sorryAx`.  This is a local check of the finite certificate, not
a complete compile of the repository's full dependency closure.

## Source-level lifting still required

The source input should be connected by proving
`binDec 3 2 = d1 ++ d0 ++ d1` and matching the swept S1 tape to the
finite start window.  The left-side pattern is determined by
`markerWord 1 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh`; positive offsets 1 through 4
are the swept blank/one boundary and the bridge's right-side marks.

For `a>0`, the expected prefix decomposition is:

1. counted left sweep of `3*a+1` cells, costing `9*a+3`;
2. the new 40-step bridge;
3. a `3*a-3`-step right scan to the original head, costing `3*a-3`.

This gives a candidate q4-prefix cost `40+12*a).  The existing q4 suffix
has cost `39+3*b`, so the total reset-prefix cost is expected to be

`79+12*a+3*b = resetPrefixCost 1 (8*k+2) a b`.

The resulting counted increment should therefore be
`proposedIncrementCost 1 (8*k+2) a b`, ending at
`S1(L,8*k+1,m=0,a+b+2,0,2^b-1,h+5+3*b)`.

These are source-level targets, not proved claims.  The q4-right-shape
argument for arbitrary `a,b,L,k`, the left-facing stream equality, the
suffix composition, and the counted drain have not yet been formalized in
this directory.  The finite trace alone does not establish the increment
macro.

## Root relevance

The candidate root extension in
`../agent8-root-residue-four/TM63RootResidueFour.lean` reaches
`m=1,n=16*r+2 = 8*(2*r)+2` after middle row 13.  This residue-two bridge
is the next natural source family to investigate.  Do not add it to the
root chain until the full source theorem compiles and passes a transitive
axiom audit.


## Kernel-checked base source connection

`M1EvenResidueTwoBaseInputCheck.lean` additionally checks the smallest
nontrivial source instance `L=3,n=2,m=1,a=1,b=0`: the actual encoded S1
configuration runs for 12 original TM63 steps (the `3*a+1` left sweep),
lands in state 3 at head `-4`, and agrees cell-for-cell with the finite
bridge start on all sixteen offsets `-11..4`.  This is a closed
`decide` proof, with `#print axioms` showing only the standard
`propext, Classical.choice, Quot.sound` axioms.

The base check validates the intended source-window orientation for this
single parameter instance.  It does not prove the quantified
`a,b,L,k` source-frame theorem.
