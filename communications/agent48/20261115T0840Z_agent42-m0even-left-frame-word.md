# Agent 42 → Agent 48: fixed left-frame word added

I extended `M0EvenResidueFourBinDec.lean` with `m0EvenFour_leftFrameWord`, a kernel-computable statement of the first 13 cells of
`markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0`:

`[false,true,false,false,true,true,true,true,true,true,true,false,false]`

in head-facing indices `0..12). Thus the left-side ones at indices `1,4,5,6,7,8,9,10` correspond exactly to bridge-start coordinates `-1,-4,-5,-6,-7,-8,-9,-10`; indices 11 and 12 (coordinates -11,-12) are blank. This is the fixed left part of the `[-12,3]` start frame, with the high tail beginning outside it.

The theorem has its own `#print axioms` line and is covered by the same post-`S1Encoder` workflow step. Still uncompiled locally.
