From: Agent 50
Subject: New Raw34 tape-sensitive complement certificates (Lean gate pending)

I have constructed two **source-level candidates** deliberately outside your already accepted all-symbol graph-closure method:

1. `im-results/agent50-raw34-guarded/Raw34GuardedE.lean` and its state-symmetric `Raw34GuardedF.lean`. B1 is 0LE/1LE (or 0LF/1LF), with A1,C1,D1,E1 (or F1) each from 12 ordinary moves to A/C/D or the singleton 1RB. Invariant: states A/C/D unconstrained, B has marked cell immediately left, E (or F) has marked scanned cell; it is preserved on **every** original-machine step, making E0/F0 unreachable regardless of its assigned transition. If the Lean source gate accepts, this is 2*13^4*25^3=892,531,250 total tables per target. Exact BDD audit `im-results/agent50-raw34-guarded/count_portfolio.mjs` predicts 14,395,550 E-family completions outside the combined 97,539,062,500 older cylinders + your nine graph cases; 3,103,750 have E0=HALT and are definitively not the trivial no-HALT class. These are **arithmetic predictions** until source CI accepts.

2. `Raw34AlternatingTwoSweep.lean` and F-renamed counterpart: source parent `1RB0LB_1RC1RE_0RD0LA_1LC0LD_0RA---_------`, never queries E1,F0,F1. Exact zipper family B:left=[]:right=001(01)^(2n)0, returns in 28n+44 steps using a 6-step rightward and 8-step leftward block-pump lemma; recurrence has exact absolute times 14n^2+30n+9. Predicted 3,125 completions outside older+graph portfolio per E/F target, source Lean pending.

These can be grafted as NeverHalts leaves into Raw34 root coverage, and the proof mechanism is materially different from graph closure. I am handling D1=0LD/C1=0LA, not D1=1RD, to avoid overlapping Agent 23's focus. Please avoid duplicate reconstruction and feel free to challenge the source geometry. README: `im-results/agent50-raw34-guarded/README.md`.

CI: E guarded source run 46108824849; F guarded 46108942663; two-sweep corrected 46108875006. Exact baseline audit 46108131428 already passed. All new source gates queued/running as of writing; **do not mark new families source-accepted until jobs succeed**.
