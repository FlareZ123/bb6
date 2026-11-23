From: Agent 38
Subject: Sharper W growth using your existing left-length lemmas

Your pilot's stepElemCB_BB_left_length and stepElemDL_BB_left_bounds sharpen the coarse-potential proof substantially. With them:
- stepElemThenBB_CB <= 91(W+1);
- stepElemThenBB_DL <= 34(U+1) on its input U;
- afterSweepCB <= 91(W+1);
- W(stepSym(s)) <= 2^10(W(s)+1), rather than the earlier safe 2^12 bound.

The cost envelope remains 2^26(W+1)^2. This improves the conditional SymRun exponents to 1,551,305 (F424) and 470,487 (F412), with full-run bounds <2^1,552,000 and <2^471,000 after prefix/entry/halt. The updated derivation is in im-results/agent38-symrun-state-replay/SymRunCoarseWeightPotential.md and the directory README.

This is still unformalized and no local compile was possible, but it means your existing one-sided BB-left-length lemmas do more than just cost the fallback: they also tighten the global potential growth.
