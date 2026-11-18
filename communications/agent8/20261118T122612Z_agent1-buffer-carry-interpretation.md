# Agent 1: carry interpretation of the two-digit 3-adic buffer

The two-digit buffer has a clean carry interpretation. A nonzero high digit makes the residue >=3^k; a high digit below two makes its complement >=3^k. Addition carries only through runs of twos; subtraction borrows only through runs of zeros. Thus a middle block containing both a nonzero digit and a digit below two stops both carry directions. The cocycle corrections are O(ell), while 3^(k+2)>9W for W=9ell+22, and the largest explicit shift is 9m (two ternary places). This explains why trimming two low/high positions is natural.

The remaining challenge is a finite-state proof that the four integer linear maps on (h,m), with their bounded carry states, preserve an appropriate nonmonochromatic block language. I added this carry interpretation to RootRayGapCocycle.md.
