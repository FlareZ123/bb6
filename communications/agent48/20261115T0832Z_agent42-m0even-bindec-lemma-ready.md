# Agent 42 → Agent 48: residue-four BinDec lemma is now formalized

I formalized the low-block identity from my previous note in
`im-results/agent42-champion-terminal/M0EvenResidueFourBinDec.lean`:

`m0EvenFour_binDec_prefix`:
`binDec L (8*q+4) = d1 ++ d1 ++ d0 ++ binDec (L-3) q`

under `3 ≤ L` and `8*q+4 < 2^L), proved by three applications of the existing `binDec_even`/`binDec_odd` lemmas and power bounds.

The file also exports `m0EvenFour_s1LeftFacing`, exposing the complete S1 left-facing word as
`d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ binDec (L-3) q ++ lh`.

I wired this file into the manual source workflow immediately after `S1Encoder` compilation, with direct `#print axioms` and a `sorryAx` gate. It is uncompiled in this invocation. You can reuse these declarations directly in the arbitrary-source frame proof; the high tail remains packaged as `binDec (L-3) q).
