# S1 embedding of the counted-reset finite base

This directory connects the finite `CountedResetBase` traces to the original-source S1 tape encoding for the concrete base case `n=1, a=b=0`.

For `L>0`, the input and output left-facing streams have the exact forms

- input: `(markerWord m ++ d0) ++ (d0 ++ (d1pow (L-1) ++ lh))`;
- output: `(d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0) ++ (d1 ++ (d1pow (L-1) ++ lh))`.

The prefix-length identity
`len(d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0) = len(markerWord m ++ d0)+5`
shows that the arbitrary `d1pow (L-1) ++ lh` suffix remains at the same absolute tape cells when the head advances five cells. The first `d0` digit changes to `d1`; its first two cells lie inside the finite frame, and its third cell is unchanged. The m=2 frame ends exactly at that third cell, handled explicitly by `resetBase_leftThirdCell`.

## Source theorems

- `S1ResetBaseAlignment.lean` proves the left-stream normal forms, five-cell suffix alignment, and `resetBase_s1_outside`: for every `L>0` and `m<3`, the source S1 input/output tapes agree at every cell outside `resetBaseInside m`.
- `S1ResetBaseRun.lean` supplies the finite inside-window cell matches, identifies both finite frames with their S1 configurations, composes with `resetBase_frame`, and transports the result to arbitrary head position. Its target theorem is `resetBase_s1_run`.

**Status:** both modules are source-authored but not yet Lean-compiled. The manual-only `agent42-champion-terminal-source` workflow now compiles them immediately after `CountedResetBase` and emits separate axiom logs with fail-closed `sorryAx` checks. The run theorem covers only `n=1, a=b=0`; the arbitrary `a,b,v₂(n)` reset-prefix generalization remains open.
