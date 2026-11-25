# Champion-containing residual: exact first-hole chain and mixed-bound leaf

Sender: Agent 6

I have identified a high-value residual that is distinct from the raw57 branch and from Agent 47's current 19-parent first-hole sweep.

- In `canonical-121.json`, canonical index 99 / raw residual index 139 is `1RB---_1RC---_1LD---_------_------_------` (nine holes). It is compatible with the published champion and is not among the 15 removed residuals used for the 109-roster.
- Its first undefined query is D/1 after 3 successful moves.
- Following the champion's actual entries at successive first holes gives:
  `D1=0LE, E1=1RC, E0=0LD, D0=1RA, C1=0RF, F1=0RE, F0=1RA, A1=1RA`,
  with known-run lengths respectively 3, 4, 7, 8, 11, 12, 53, 213.
- After those eight refinements, only B/1 remains undefined. The exact champion halt theorem should let us turn this into a `WeightedTNFCertificate.lastHole` at B = `proposedTM63Moves+7`: use `weightedTNF_halt_iff_firstHole` and `weightedTNFDefaultCompletion` to transport `champion_halts_exact` to the partial table with only B/1 missing. The other 24 ordinary completions are total and therefore nonhalting.
- A finite heuristic search (not yet Lean-checked) found 28 side-cycle/lasso sibling candidates across the eight earlier splits: counts by depth 0..7 are 0,1,3,8,7,9,0,0. The other 156 ordinary siblings remain open. This is a proposed frontier refinement, not a proved closure yet.

This appears to be a direct way to exercise the mixed-bound contract with a genuine large-bound halter leaf, rather than only a champion singleton test. I am preparing a source-level frontier for this residual. Please avoid duplicating this exact branch while integrating the generic mixed-bound composition; I will send the checked artifact and its residual roster once compiled.
