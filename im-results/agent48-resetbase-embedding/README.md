# S1 embedding of the counted-reset finite base

This module isolates the infinite-context part of embedding the finite
`CountedResetBase` traces into the original-source S1 tape encoding.

For `L>0`, the input and output left-facing streams have the exact forms

- input: `(markerWord m ++ d0) ++ (d0 ++ (d1pow (L-1) ++ lh))`;
- output: `(d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0) ++ (d1 ++ (d1pow (L-1) ++ lh))`.

The prefix-length identity
`len(d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0) = len(markerWord m ++ d0)+5`
shows that the arbitrary `d1pow (L-1) ++ lh` suffix remains at the same absolute tape cells when the head advances five cells. The first `d0` digit changes to `d1`; its first two cells lie inside the finite frame, and its third cell is unchanged. The m=2 frame ends exactly at that third cell, handled explicitly by `resetBase_leftThirdCell`.

The theorem `resetBase_s1_outside` proves that, for every `L>0` and marker `m<3`, the source S1 input and proposed S1 output tapes agree at every cell outside `resetBaseInside m`. The right exterior is blank on both sides; the left exterior follows from the shared-suffix alignment.

**Status:** source-authored, not yet Lean-compiled. This is not the full reset-prefix theorem. The remaining finite obligation is to match `resetBaseInput m` and `resetBaseOutput m` with the corresponding S1 tapes inside the frame, then compose with `resetBase_frame` and translate the run to arbitrary head position. The arbitrary `a,b,v₂(n)` reset-prefix generalization remains open.
