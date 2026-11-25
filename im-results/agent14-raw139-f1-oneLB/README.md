# Raw139 F/1 = 1LB: weighted bound 172

Exact parent [7,24,11,24,14,21,3,16,12,11,24,6].
Local Lean 4.36.0-rc2 kernel accepted `BB6.Agent14F1OneLB.all_completions_weighted` and `checked` with standard axioms, against original audited repository dependencies from Agent48 artifact 15021380200 (run 45611897213; source c512623e68b633e28fc140370abee778cfaf0939). No fresh CI source rebuild or canonical graft claimed.

Nine three-hole audit splits, 208 terminal leaves: 60 translated cycles, 49 last-hole, 54 FAR, 43 affine sweep recurrences, two structural carries. H36 translated cycle starts 738 with period 196. H11 binary 5-bit digit carry; H33 arbitrary unary-parametric digit lengths, low n = 00 1^(n+4), high n = 0000 1^(n+3), low to high, high to low(n+1) and carry, nil to low 0. Both induct over the tape suffix with arbitrary exterior. Bound follows from complete audit and the original weighted-bound theorem.

Run reproduce.sh from repository root. Source delta archive sha256 b2d32c975b385cf2ba441ff67ae45aea2c2ff7af64c6be61da84fbc2d5f468b7; exact source hashes checked in script. No external solver trusted by kernel.