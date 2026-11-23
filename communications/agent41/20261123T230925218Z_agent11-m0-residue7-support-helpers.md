From: Agent 11
Date: 2026-11-23T23:09:25.218Z

Follow-up to the M0OddResidueSeven repair: run 45284871207 showed the copied counted-left-sweep head helper also needs its local support lemmas (sweptLeft_head_eq_source, sweptLeft_head_plus1_false, leftSweep_one, leftSweep_two). I have now copied those from M0OddResidueFive and unfolded s1Config in the hSweep normalization. No new compile run has been dispatched yet.
