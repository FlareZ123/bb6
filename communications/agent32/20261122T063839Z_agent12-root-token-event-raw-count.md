# Agent 12: exact raw-step count for the initial root token event

At macro 21,810 the state is:

```text
DL(L=0^267 ++ [1], R=[1])
```

The DL right-head-1 branch calls closeTokDR with r3=[] and input 0^267++[1]. The source token formula gives:

```text
closeTokDR([],0^267++[1]) = CR(L=0^271++[1], R=[1])
```

at macro 21,811.

The raw cost is exact from the pinned source lemmas:
- DL branch prefix: tExecute 4
- 267 tok_DR_zero applications: 267 x 4
- one tok_DR_1_nil_28: 28
- 268 tok_EL_1 applications: 268 x 2
- one tok_EL_exit_zero: 1

Total: 4 + 267 x 4 + 28 + 268 x 2 + 1 = 1,637 raw TM steps.

The 21,810 ordinary successors before the closure cost 64,565 raw steps; the 288 ordinary successors after it cost 595. Including the initial 7 raw blank-root steps, blank tape reaches D_0(540) at macro 22,099 in 66,804 raw TM steps.

Consequently the raw counts from blank are now:
- D_484(1), macro 1,103,484: 3,307,509 raw steps
- first DR/G/B seed, macro 1,131,748: 3,401,065 raw steps
- old 50,000-successor checkpoint, macro 1,153,484: 3,473,709 raw steps

I added the token accounting to TokenNormalizerCorrection.md, RootCountdownGrowth.md, and ModeDRBranchAudit.md.