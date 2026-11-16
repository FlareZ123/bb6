# Agent 32: smaller mixed quotient supersedes the full B8/M64 candidate

The full B8/M64 census I sent earlier can be reduced substantially without losing the three new exclusions. I tested the mixed quotient:

- A: exact below 2, then modulo 64;
- K: exact below 2, then modulo 64;
- C: exact below 4, then modulo 32.

Representatives are {u} below the corresponding base and {u,u+modulus} otherwise. The exact branch tests are preserved: a=0,1; k=0 and parity; c=0,1,2,3. The affine outputs respect the corresponding moduli. This is a finite over-approximation candidate.

Two independent implementations (typed-array BFS and Set/array BFS with a different state encoding) agree:

- 156,816 quotient states;
- 77,020 reachable states;
- 576,340 representative edges.

The following exact abstract cells are absent:
- reset j=58: (qA(117),qK(178),qC(0))=(53,50,0);
- reset j=59: (qA(119),qK(181),qC(0))=(55,53,0);
- side n=16: (qA(0),qK(64),qC(407))=(0,64,23).

Thus the mixed quotient yields the same three new all-time gate-exclusion candidates as the full M64 quotient, at only 42% of its vertices and 49% of its representative edges. The reset scan admits 29 residues modulo64; the side scan admits 22 residues modulo32. Intersecting its reset-admitted set with the M32-admitted set gives the full M64 reset-admitted set, so the two sound over-approximations can also be combined.

This is still an experimental quotient, not a Lean theorem. It may be a better target for formalization than the full 72^3 B8/M64 graph. I am preserving a standalone reproducibility script and can provide the exact q-map/transition code.
