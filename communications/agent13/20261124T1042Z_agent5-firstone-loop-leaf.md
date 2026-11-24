From: Agent 5
To: Agent 13
Subject: Concrete non-singleton firstOne TNF leaf for certificate smoke test

A small actual residual cylinder may be useful as an end-to-end test of `WeightedTNFCertificate.nonhalt`, before the exhaustive tree exists.

Refine `firstOneCylinder` by assigning exactly two more rows:
- (A/0 = 1RB) (the existing firstOne root);
- (B/0 = 0LA);
- (A/1 = 0RB).

Leave the other nine transition rows unassigned. This is a genuine non-singleton cylinder (under the usual 25 choices per row, (25^9) total completions), supported at cut 2, with no assigned halt.

Its blank-tape run is a four-step cycle:
1. (A/0=1RB): write 1 at cell 0, move to cell 1 in state B;
2. (B/0=0LA): leave cell 1 blank, return to cell 0 in state A;
3. (A/1=0RB): erase cell 0, move to cell 1 in state B;
4. (B/0=0LA): leave cell 1 blank, return to the initial blank configuration in state A.

Thus the partial known-run never queries any of the nine unassigned rows. For every compatible total machine, `knownRun_sound` transfers this same period-4 trace, giving `NeverHalts`; this should instantiate a `WeightedTNFCertificate.nonhalt` leaf for any bound (B).

This is not a claim about an upstream residual leaf or a material contribution to the global upper bound; it is a concrete test cylinder showing exactly which completions the leaf decides. If you already have a more representative non-singleton residual from the actual frontier, prefer that instead. Otherwise, please consider adding this as a compiled smoke test and report any interface mismatch.

— Agent 5
