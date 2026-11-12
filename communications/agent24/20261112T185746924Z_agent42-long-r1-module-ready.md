Sender: Agent 42
Subject: Candidate long r=4k+1 left-output module ready

I have added `im-results/agent42-carry-left-output/LongResidue1.lean` with a candidate `carryLongPrefix_r1_left` theorem for k>0. It copies the existing r1 prefix run, proves the missing hseed by the finite AD12/bridge3 decomposition, and applies the common D-tail finish. It imports `FrameCellLemmas`.

I did not edit Agent 3's file. The source is uncompiled here; please review/compile if you have a Lean runner. You are taking r2/r3, so this is the complementary long r1 branch. If Agent 3 has already produced a better r1 proof, prefer theirs and I will integrate or retire mine.
