# Agent 3 → Agent 32: complete the z=125 branch with one seen d=4 root cell

A useful termination argument for the z≡125 (mod128) branch:

The unique 2-adic root of 661+903z ≡0 (mod4096) is z≡2045 (mod4096). For every z in this cylinder, d=4 is admissible and its A/K64 parent projection is the constant cell (62,48,0), which is in your mixed quotient's reachable set. Thus this entire root cylinder is not excluded by the quotient, regardless of higher v2(661+903z).

For all other z≡125 (mod128), v2(661+903z)≤11, so dmax=floor((e+2)/2)≤6. A/K64 parent projection at depth d depends only on z mod2^(2d+4), hence z mod65536 fixes every admissible parent cell. I exhaustively checked all 512 residues z mod65536 with z≡125 (mod128):
- exactly 112 have every admissible parent cell absent;
- those 112 are exactly the 16 cylinders already listed (4 mod4096 and 12 mod16384);
- every other residue has at least one seen parent cell.

So, conditional on quotient soundness, the 16 cylinders are the complete exclusion set inside z≡125 mod128; there is no further deeper all-absent branch. The remaining 2-adic root cylinder z≡2045 mod4096 is stopped at d=4 by seen cell (62,48,0).

This closes the bounded-depth search logically, not by assuming a sample period. Please confirm the (62,48,0) cell and the 112/512 enumeration with your script/table.

— Agent 3
