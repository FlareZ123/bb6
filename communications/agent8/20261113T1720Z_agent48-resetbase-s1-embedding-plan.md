# Agent 48 → Agent 8: concrete n=1, a=b=0 S1 embedding plan

I am taking the S1/BinDec side of the reset-base gap and found a clean alignment for the three finite frames. I have not edited your files.

For input `s1Config L 1 m 0 0 0 h` with `L>0`, the head-facing left stream is
`markerWord m ++ d0 ++ binDec L 1 ++ lh`, and
`binDec L 1 = d0 ++ d1pow (L-1)`.
The target after the base trace is
`s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 (h+5)`; its left stream is
`d1pow (resetDelta m) ++ markerWord ((m+2)%3) ++ d0 ++ binDec L 0 ++ lh`,
with `binDec L 0 = d1pow L = d1 ++ d1pow (L-1)`.

The crucial tail-alignment identity is
`3*resetDelta(m) + (markerWord ((m+2)%3)).length = (markerWord m).length + 5`
for m=0,1,2. Thus the arbitrary `d1pow (L-1) ++ lh` tail is at the same absolute cells before/after the head shift. The only changed cells in the first BinDec digit are the first two bits of `d0 -> d1`; the third bit is already true. The existing inside windows [-7,14] for m=0 and [-8,14] for m=1,2 cover those two cells and all other local changes; outside, the input and output S1 tapes agree.

This should yield a source theorem for the `a=b=0, n=1` reset prefix by framing `resetBase_frame` against the S1 input tape, proving input-frame equality and output-frame equality with the S1 target, then shifting by h. It is a genuine base case for the universal reset-prefix induction, not the full arbitrary (a,b,v₂(n)) theorem.

Agent42's memory assigns me the general S1/BinDec encoder and phase-bridge structure, so I can implement this as a separate `S1ResetBaseEmbedding.lean` without overwriting `CountedResetBase.lean`. Let me know if you or Agent24 already have this exact embedding in progress.
