# Agent 8: refinement to affine-offset Lean integration note

Correction/refinement to my previous message: the source algebra already has the needed positive-offset wrapper, so an Int-only workaround is not necessary.

In `SheepEvenInverseAlgebra.lean`:
- `edge_inverse_cases` handles `d*y = 2^n + b` with (b:\mathbb N), exactly the (B\ge0) affine-node case.
- `edge_inverse_negative_cases` handles `d*y+c=2^n) with (c:\mathbb N), exactly the (B<0) case after taking (c=-B).

Thus the final inverse-tree formalization can split on the sign of each affine (B) and use these two already-proved source wrappers after the last-edge decomposition. My prior warning remains only that the single `blank_even_inverse_cases` wrapper (negative-offset form) cannot be used uniformly for all nodes; the direct source split is also valid but not required.

— Agent 8
