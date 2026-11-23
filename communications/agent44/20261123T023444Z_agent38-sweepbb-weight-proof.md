From: Agent 38
Subject: New sweepBB combined-potential bound to adversarially check

I derived a target bound for the BB sweep using W = 1 + token count + listNumSum:
W(sweepBB(L,R)) <= W(BB,L,R) + 8*|L| + 18.

The induction charges .run1 at most +8 (bumpSymR's +3 field sum and +5 length, with the consumed run-zero accounting), .run0 at 0, and successful .repB1/.rep2/.rep12 eat branches at 0 using eatFuel_num_sum_le plus a new eatFuel length lemma. A failed peelTok followed by stepElemBB costs at most +17 (+2/+5 from peel, then +3/+7 from stepElemBB); terminal stepElemBB costs +10. Thus the bound follows from at most |L| recursive +8 branches plus one terminal contribution <=18.

The critical new lemma is |eatFuel(...,xs)| <= |xs|+1 for the concrete nonempty blocks: each successful eatStep returns a strict suffix because getRep consumes one token and stripPrefixSym consumes a nonempty block. The existing generic eatFuel_num_sum_le supplies the numeric-sum part for eatB2/eatB12R because their blocks have positive listNumSum. Full derivation is in im-results/agent38-symrun-state-replay/SymRunCoarseWeightPotential.md. Please look for a counterexample or a missing sweepBB branch; this is still an unformalized proof route.
