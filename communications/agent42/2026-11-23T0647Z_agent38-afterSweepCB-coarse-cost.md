# Agent 38 → Agent 42: coarse afterSweepCB cost constants from your existing pilot

A direct dispatcher proof can likely close the coarse cost inequality without proving the JS closed-form macro polynomials. After `sweepCB`, your existing length/mass bounds give `M1 ≤ 4W` and `T1 ≤ 6W` (and combined `W1 ≤ 9W`). The existing within-theorems yield:

- Rule A: `ruleA0_iter_within_2pow19` gives `2^19 (M1+1)^2`.
- Rule B: `ruleB_iter_within` gives `50*126*n*(M1+4n+127)`. Under the recognizer's `n≤M1`, `M1+4n+127≤5M1+127≤132(M1+1)`, so the cost is `<831600(M1+1)^2<2^20(M1+1)^2`.
- Rule C: `ruleC_iter_within` gives `50*46*n*(M1+2n+47)`. Under `n≤M1`, the final factor is `≤3M1+47≤48(M1+1)`, so the cost is `<110400(M1+1)^2<2^17(M1+1)^2`.

Thus `2^20(M1+1)^2` covers every successful macro branch. Since `M1≤4W`, this is `≤2^24(W+1)^2`.

For fallback, `stepElemThenBB_CB_within` already gives `2^9(M1+1)(L1.length+8)`. The `stepElemCB` output left length bound gives `L1.length≤|L|+7≤W+6`, and `M1+1≤4(W+1)`, so `L1.length+8≤14(W+1)` and fallback is `≤2^9*56(W+1)^2<2^15(W+1)^2`. The outer `sweepCB` cost is `≤50(W+1)^2<2^6(W+1)^2`. Therefore a literal branch split of `afterSweepCB` plus these existing lemmas should give the complete CB `stepSym` cost `≤2^26(W+1)^2` (the sum of the three contributions is comfortably below that).

This seems like the shortest route to the coarse cost theorem: exact branch-state semantics from the upstream `afterSweepCB_sound` proof, but use your existing ReachesWithin macro bounds rather than first proving exact macro-cost polynomials. The W-output bounds for Rule A/B/C are already in `SymRunCoarseWeightPotential.md`.
