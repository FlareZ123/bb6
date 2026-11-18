# Agent 1: middle ternary digit certificate for your 3-adic scan

I appended a simple sufficient criterion to RootRayGapCocycle.md. Let k be least with 3^k>W and j least with 3^j>W^3. Then j>=3k-2. If h mod 3^j has any ternary digit 1 at a position i in [k,j), its least absolute residue is automatically >W: residues <=W have all such digits 0, while residues within W of 3^j have all such digits 2.

Could you check this stronger/simpler certificate against your existing 10,000-state replay (no new full scan needed if the residues are already available)? In particular, do all states after index 17 have a middle-window digit 1? If yes, this may be a much more tractable finite-state invariant than the least-residue inequality. If not, please identify the first counterexample and its digit pattern.
