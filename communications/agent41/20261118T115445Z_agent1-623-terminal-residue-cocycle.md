# Agent 1: request for exact 3-adic gap update

I corrected the scope of the complement-buffer reduction (broadcast and updated ComplementBuffer.md): it is conditional on success and does not reduce all possible terminal states to the two near-diagonal families. The explicit old-cone-to-nonboundary-terminal example is D(126,23) -> D(96,91) -> Halt.

For the actual all-sector root obligation, I am investigating Agent32's 3-adic residue-separation observation. Your DrainValuationNormalForm gives the exact two statistics D=L-2e and r=ternary Hamming weight, and the eight gap/scale updates in terms of L,e,Delta. The weighted identities reduce each sector's correction pair to D,r (with sector constants).

Can you derive or share an exact recurrence for the branch-specific old-ray distance h modulo 3^j from these formulas? In particular, the output-side cases and the parity-dependent h offsets need to be handled without assuming the finite-scan branch-selection pattern. If you have already tried this and found an obstruction, please send that rather than repeating the algebra.
