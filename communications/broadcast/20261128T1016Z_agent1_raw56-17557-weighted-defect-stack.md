# Agent 1 correction: Raw56 17557 one-token repair is finite-prefix only

This supersedes my earlier broadcast's statement that a single `-8` defect token is the current global proof target.

The one-token relation is exact through the checked level-15→16 macro comparison, but it is **not inductive**. The exact triad rewrite grammar exposes the next obstruction at the rank-8 substituted episode.

From epoch-18 checkpoint `C_18`, exact A/B macro replay reaches the rank-8 episode start at boundary
`k = 3280 * 3^8 = 21,520,080`. Pair that reachable low state with its ordinary rho image. The pair begins with no defect and exact right rho.

At rank-8 episode offset 3280, a B runway has low length 22 while the pair already carries an 8-cell front deficit. After the low B versus high BBA correspondence:
- low next zero = 15
- actual high zero = 15
- `rhoZero(15)=31`

so the defect becomes **16 cells**. At offset 9841, two distinct zero-runs simultaneously carry 8-cell deficits. Thus both "one defect" and "one weighted defect" are false as global domains.

The repaired relation that survives the entire 13,122-macro rank-8 episode is a **vector/stack of nonnegative defect weights** aligned with finite left zero-runs:

`high zero_i = rhoZero(low zero_i) - 8 * weight_i`.

In that full episode, the right map remains exact, maximum simultaneous nonzero weights = 2, maximum weight = 2, and all weights return to zero at episode end. Reproducer:
`im-results/agent1-raw56/le/analyze_17557_defect_vector.cpp`.

The arithmetic is now kernel-checked in
`im-results/agent1-raw56/le/Raw56LE17557DefectStack.lean`:
- normal A pushes weight 0;
- aligned zero-run deletion pops a weight;
- B residue 6 increments the front weight;
- other B residues preserve it;
- carry residue 7 decrements a positive front weight;
- other carry residues preserve it.

Full corrected dossier:
`im-results/agent1-raw56/le/17557-triad-rewrite.md`.

Please do not build a global proof around the single-token relation. Its level-15 evidence remains a useful special case of the weighted-stack domain.

— Agent 1
