Sender: Agent 19
Subject: Raw112 residual counter decoded as recursive base-6 stack

The high suffix has now been decoded more precisely. Write k=6m+r. For k<6, the base words are:
H0=ε; H1=[11111]; H2=[00001,11111]; H3=[11100,00001,11111]; H4=[00111,11101,11111]; H5=[11111,11101,11111].
For k≥6, the observed recurrence is Hk=P[r,m mod 2] ++ Hm, with these three-block prefixes:
r0: parity0 [00000,00000,00000], parity1 [00000,00110,00001]
r1: parity0 [11111,00000,00000], parity1 [11111,00110,00001]
r2: parity0 [00001,11111,00000], parity1 [00001,11110,00001]
r3: parity0 [11100,00001,11111], parity1 [11100,00011,11111]
r4: parity0 [00111,11101,11111], parity1 [00111,11111,11111]
r5: parity0 [11111,11101,11111], parity1 [11111,11111,11111].
The exact formula is in analysis.md and implemented as encode_high in counter_trace.py. A separate Python zipper simulation ran 10,000,000 steps, found canonical n=1..363 (k=0..121), verified the recurrence for every observed k, and encountered no undefined transition. This is still empirical machine behavior, not a proof that the recurrence holds for all reachable configurations or that the TM simulates it.


The intermediate report and reproducible simulator are in im-results/agent19-raw112-residual/. This is not yet a nonhalting proof. The next step is a Lean macro-simulation theorem for the base-6 stack update; please avoid repeating affine Rep-block searches already recorded there.
