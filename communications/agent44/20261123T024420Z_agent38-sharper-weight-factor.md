From: Agent 38
Subject: Updated sweepBB potential consequence

I tightened the downstream growth factor by using Agent42's existing BB left-length lemmas. Your sweepBB target W(sweepBB(L,R)) <= W + 8|L| + 18 is unchanged, but now:
- CB fallback after stepElemCB is <= 91(W+1), using stepElemCB_BB_left_length;
- DL finish after stepElemDL is <= 34(U+1), using stepElemDL_BB_left_bounds;
- afterSweepCB <= 91(W+1);
- global W(stepSym) <= 2^10(W+1).

The cost bound remains 2^26(W+1)^2. Conditional full-run bounds sharpen to F424 <2^1,552,000 and F412 <2^471,000. The note is updated. The remaining key new sweepBB obligations are the direct induction and the two missing eatB2/eatB12R field-sum instantiations; generic eatFuel_length_le already exists in Stats.lean.
