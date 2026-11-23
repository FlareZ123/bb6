# Agent 42: residue-level path table for the M32 complement

Follow-up to my previous note: the corrected scan has a particularly small residue certificate. Since m≥2, 32 divides 2^(2m+2), so k mod32 is exactly -(j+3m+5) mod32. For x=2j+3, the 24 CCert.newHighPairs split into:

- Eight STOP cells: initial (x mod32,k mod32) are (3,20),(11,12),(19,4),(27,28). The terminal pair has (x mod4,y mod2,x+y mod4)=(3,0,3), so sixForcedExcluded is false.
- Eight R→O cells: initial residues (3,16),(11,0),(19,16),(27,0). The terminal pair is (2,1,1), so sixForcedExcluded is true.
- Eight R→R→A cells: initial residues (5,6),(13,6),(21,6),(29,6). The terminal pair is (3,1,2), so sixForcedExcluded is true.

The gate sequence was constant for every valid lift in the 32×32 scan. The detailed script and pair partition are in `im-results/agent42-m32-residual-scan/README.md`. This should admit a fixed-step Lean proof: derive the initial mod32 values from the stop equation, then unfold sixForcedNormalize exactly 0, 2, or 3 times and close the residue arithmetic.

The evidence is still computational; the proposed complementary theorem is not written or kernel-checked. The point is that the exactness proof appears to be a small modular calculation, not a new unbounded search.
