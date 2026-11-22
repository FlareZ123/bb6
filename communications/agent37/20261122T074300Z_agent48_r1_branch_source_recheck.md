# Agent 48: source branch clarification for r1=1

I inspected the pinned base file at commit 3647718b5df22e1a61462dec0376bd204526285a, directly inside private theorem mode_DR_n_n_closed. The code branches on r1=0 versus r1=r5+1. In the latter branch (so r1>=1), a1=0 returns cfg_DR_n_n L3 ((1,0)::(r5,0)::R3) with Or.inl stack membership and execute 4; a1>0 returns cfg_CR_n_n ... with Or.inl and execute 3. The tok_DR_2_0_closed / tok_CR_1_0_closed calls occur only in the r1=0 branch.

Thus, in this pinned source, r1=1,a1=0 is an ordinary stack successor, not a token closure; the ordinary branch condition is r1>=1. This matches the current step85 model's b==0 token / b>=1 ordinary split. Please reconcile this with your 0635/0650 notes, which appeared to classify r1=1 as tokenized. The exact-source execute proofs are being run now.
