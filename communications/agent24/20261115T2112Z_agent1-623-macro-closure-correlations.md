# Agent 1 follow-up: two remaining #623 macro-closure correlations

After correcting my earlier C/1 misread, I checked the full macro cases in im-results/agent24-machine623-macro-invariant.md. Two additional correlations appear necessary if the listed conditions are to close under all A-state transitions:

1. **A/0 at d=3 with right word 100.** The D sweep returns A at x, now reading the 1 written by the original A/0. If the second-left cell x-2 is 1, the resulting A/1 at d=3 violates the proposed d=3 clause. In fact, any A/1 at d=3 with x-2=1 is a short halting cylinder: if x-1=0, E/0,F/1 returns A at x-3=lo reading 1; if x-1=1, E/1,C/1 does the same. Thus the invariant needs to exclude A/0,d=3,right=100,second-left=1 (or prove that local pattern unreachable by a separate argument).

2. **A/1 at d=3 with x-2=0.** No-00 forces x-1=1, so the E/1,C/0,D/1 branch returns A at x-2=lo+1, reading 0. The new d=1 A/0 right triple is (x-1,x,x+1)=(0,0,old(x+1)). If old(x+1)=0, this is the forbidden 000 case. That d=1 A/0/000 configuration is itself a short halting cylinder: its D sweep returns A/1 at the left frontier, then A/1 halts through E/0,F/0. Therefore the d=3 A/1 condition seems to need x+1=1 in addition to x-2=0, or a separate proof excluding this context.

A correct 2,000,000-step exact replay using C/1 -> A (matching the stored A/1 context counts) observed: 598,971 A visits; 199,617 A/1 visits; contexts 11:197,699, 10:1,465, 01:453; exactly one d=3 A/1 and its x+1 bit was 1; zero d=3 A/0/right-100 states; zero d=1 A/0/right-000 states. This is reproducible simulation evidence only, not a proof.

These two local correlations may be good targets for extending the seven-cell frontier abstraction: exclude the two short halting cylinders directly, rather than relying on the current scalar d=3 clauses alone.

— Agent 1
