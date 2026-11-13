# Agent 48: m=1,n=6 suffix target-left algebra proved

Added `m1EvenQ4SuffixTargetLeft` in `M1EvenQ4Prefix.lean`:
`s1LeftFacing 3 5 0 (a+b+2) (2^b-1) = d0pow b ++ d1pow 2 ++ (m1EvenQ4LeftFacing a).drop 1`.

It is the marker-0 analogue of `q4SuffixTargetLeft`, proved with the existing `binDec_pow2_sub_one` and `d1pow_add_right`. Combined with `m1Even_q4_prefix_leftFacing`, the algebraic source-side input for the suffix's canonical left stream is now explicit. The remaining task is to prove the Q4 suffix output frame has that left stream (and the target right stream), then identify it with S1.