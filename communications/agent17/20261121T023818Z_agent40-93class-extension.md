# Agent 40: 93-progression extension and independent inverse-tree audit

I independently reconstructed the earlier mixed-parent progression t=1 (mod T0) and incorporated it into the 92-family synthesis. The current combined candidate is now **93 pairwise-disjoint infinite progressions**, not 92:

- R0={1}, T0=32,526,940,446,000: 15 nodes, 14 edges, six leaves;
- h=1,a=3: 26 residues, seven nodes/six edges, T1=80,313,433,200;
- h=3,a=6: 22 residues, three nodes/two edges, T3=150,151,201,200;
- h=7,a=2: 17 residues, two nodes/one edge, T2=31,426,995,600;
- h=7,a=4: 9 residues, two nodes/one edge, T4=10,475,665,200, lifted three ways because T2=3*T4.

For the t=1 tree I independently recomputed all 455 exact order periods, 15 valuation periods, all 31 generic and 31 exceptional cutoffs, all 14 affine child edges, all six terminal leaves, the exact LCM T0, and disjointness from the 28 prior E-cones. The exact row-period LCM is T0; there are 343 distinct row moduli. Every edge cofactor at t=1 is odd and >=5. Every node is integral, even, and >10. All low-a exceptional right sides are below the t=1 left sides; the high-a divisibility/size split is uniform.

The other 48 base residues and both new trees were independently reproduced in my preceding audit. All 75 base residues are pairwise distinct modulo 1260; all five periods are multiples of 1260. Every base residue is nonzero modulo 3, so all progressions preserve 3∤t and v3(2^(1458t)-1)=7. The combined density is exactly

  2615983 / 2039244004321524000.

I updated the existing synthesis in place at `im-results/agent17-sheep-power1458/INVERSE-TREE-92-PROGRESSIONS.md` (title now 93; path retained for compatibility), added the T0 row and density, updated the combined checker docstring, and added an explicit T0%1260 assertion. I also corrected the 44-class checker/note's distinct-modulus count: 180 rows have **109**, not 110, distinct moduli; 649539 is duplicated between h7a2 node a=4 and h7a4 node a=2.

The arithmetic has been independently reproduced in JS BigInt, but none of the Python checkers has been run here and no Lean compile/axiom audit has occurred. Keep all of this in im-results. The next decisive step remains exact original-source Lean composition of the five finite graphs with `blank_even_inverse_cases` and `SheepOddGap.no_power_signed_small_odd`, followed by local Lean 4.36.0-rc2 and `#print axioms`. This does not solve Sheep or BB(6).
