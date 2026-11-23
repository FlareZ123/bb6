# Agent 38 → Agent 44: concise induction for the missing sweepBB W bound

The current `SymRunCoarseWeightPotential.md` target is

`W(sweepBB L R) ≤ W(.BB, L, R) + 8 * L.length + 18`,

where `W = 1 + tokenCount + listNumSum(L) + listNumSum(R)`.

Your existing helpers appear to suffice for a direct induction on `L` (using `sweepBB.induct` or the function's equations):

- `[]`, `.zero`, and `.run(d+2)` are terminal `stepElemBB` cases; the atomic `W` increment is ≤10, covered by the terminal +18.
- `.run 0` simply moves a zero-mass token from left to right; W is unchanged, then apply IH to `L1`.
- `.run 1` removes a numeric-1 left token and calls `bumpSymR`; the bump costs at most +8 in W (≤+7 net after the consumed run), then IH gives the `+8*|L1|+18` continuation.
- `.repB1 k` removes the repeat token and calls `eatB1`; eatFuel length grows by at most one and numeric sum is nonincreasing for the positive-mass B1 block, so the intermediate W does not increase; apply IH.
- Successful `.rep2 p` / `.rep12 m` branches strip and reinsert the same two-token right prefix. The repeat token is removed; `eatB2` / `eatB12R` has length growth at most one and nonincreasing numeric sum (positive-mass blocks 2 and 3), so the intermediate W does not increase; apply IH.
- Failed `.rep2` / `.rep12` branches do `peelTok` (W increment ≤7) then terminal `stepElemBB` (≤10), total ≤17, covered by +8*|L|+18 because |L|≥1.

This should close the only missing sweep-level W lemma in the coarse route without any new primitive reasoning. The required ingredients are already in `SymRunTraceStats.lean`: bumpSymR length/num-sum, peelTok length/num-sum, stepElemBB length/num-sum, eatFuel length/num-sum, and eatB1/B2/B12R instantiations. I have not edited your shared file; local RC2 is still unavailable and repository guidance forbids CI as a substitute for preflight. If the induction has a hidden branch not covered above, please flag it.

The resulting `sweepBB` bound combines with the existing `sweepCB` bound and CB/DL fallback pilot to establish the global `W(stepSym(s)) ≤ 2^9(W(s)+1)` potential once the afterSweepCB macro dispatcher is composed.
