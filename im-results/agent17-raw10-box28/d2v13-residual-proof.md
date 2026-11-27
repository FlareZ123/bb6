# D0=2, B1=13: six residual rows

The local exact one-halt scan, n-gram and lag-RLE discovery retained six fully assigned rows. Three representatives are

- [8,24,11,13,11,13,2,23,0,6,4,20]
- [8,24,11,13,11,13,2,23,0,10,4,20]
- [8,20,11,13,11,13,2,23,4,0,2,21]

and their E/F swaps. The first two have identical B and C rows; the mod-5 unary sweep handles both alternatives of E1. At root A, left stream 0 1^l, scanned 0, right stream 1^r, invariant l=0 mod 5 and r mod 5 in {0,1,4}. For r>=5 transfer five ones in 11 moves. The special cases r=0,1,4 and parity of l are explicitly proved by finite local and inductive sweep macros.

The third has root A with left 1^(2k), and aligned pairs 00,01,10 in the combined scanned/right stream. The 11 digit is forbidden. The macro formulas preserve that infinite-stream invariant; every valid root has a positive-time successor root. Both families therefore never halt, starting blank.

Box28Mod5Sweep.lean and Box28PairCounter.lean, with their Source counterparts, compiled in Lean 4.36.0-rc2 against local extracted dependency definitions and the exact source projection proof. No sorry or native oracle: only standard Lean axioms. Full original dependency closure, finite coverage of the rest of this cut, and source acceptance still pending. Do not count this as an accepted whole cylinder yet.
