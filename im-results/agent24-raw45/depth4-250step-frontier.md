# Agent24 depth-four Raw45 frontier discovery (NOT a formal theorem)

Generated UTC 2026-11-28T01:44:54.060Z from the seven-hole literal parent `1RB---_1RC---_0RD---_1LD1RB_------_------`.

This is **exploratory candidate selection only**: first-unknown-row target first-use cutoff, exact BigInt blank zipper simulation up to **250 steps**, at most 32 prior translated-lasso candidates per step. This source-unverified tool classifies all descendants at depth four, records early cycles but deliberately does **not** claim nonhalting without source `zipCycle_sound`.

- Total visited partial nodes: 38277
- Split nodes: 1602; omitted state-first-use target aliases: 172
- Early translated-cycle candidates by depth 0..4: [0,6,153,1645,19735]
- Still-running 250-step simulations by depth 0..4: [0,0,6,65,895]
- Depth-four fifth-hole-query residuals: 14170
- Largest discovered early recurrence period: 32 moves; latest entry+period observation 194 steps
- Runtime 1.4 seconds.

First 25 unresolved 250-step examples (samples only):

```
3: 1RB1LB_1RC0LA_0RD1RB_1LD1RB_------_------
4: 1RB1LB_1RC0LA_0RD0LE_1LD1RB_---1RA_------
4: 1RB1LB_1RC0LA_0RD1LE_1LD1RB_---0LB_------
4: 1RB1LB_1RC0LA_0RD1LE_1LD1RB_---1RD_------
4: 1RB1LB_1RC0LA_0RD0RE_1LD1RB_0LA---_------
4: 1RB1LB_1RC0LA_0RD1RE_1LD1RB_0RB---_------
4: 1RB1LB_1RC0LA_0RD1RE_1LD1RB_1RC---_------
4: 1RB1LB_1RC0LA_0RD1RE_1LD1RB_0LD---_------
4: 1RB1LB_1RC0LA_0RD1RE_1LD1RB_1RD---_------
3: 1RB0RB_1RC0LA_0RD0RC_1LD1RB_------_------
3: 1RB1RB_1RC0LA_0RD0RC_1LD1RB_------_------
4: 1RB1LC_1RC0LA_0RD0RE_1LD1RB_---0LB_------
4: 1RB1LC_1RC0LA_0RD1RE_1LD1RB_---0RD_------
4: 1RB0LE_1RC0LA_0RD0RC_1LD1RB_---0RA_------
4: 1RB0LE_1RC0LA_0RD0RC_1LD1RB_---1RA_------
4: 1RB0LE_1RC0LA_0RD---_1LD1RB_1RB1RC_------
4: 1RB0LE_1RC0LA_0RD---_1LD1RB_0RB1RD_------
4: 1RB0LE_1RC0LA_0RD---_1LD1RB_0RB0LE_------
4: 1RB0LE_1RC0LA_0RD---_1LD1RB_0LB1LE_------
4: 1RB1LE_1RC0LA_0RD1RB_1LD1RB_---0LA_------
4: 1RB1LE_1RC0LA_0RD0RC_1LD1RB_---0LB_------
4: 1RB1LE_1RC0LA_0RD---_1LD1RB_0LB1RB_------
4: 1RB1LE_1RC0LA_0RD---_1LD1RB_0LB1LC_------
4: 1RB1LE_1RC0LA_0RD0RC_1LD1RB_---0RD_------
4: 1RB1LE_1RC0LA_0RD0RC_1LD1RB_---1RD_------
```

The accepted source theorem in `results/2026-11-28-raw45-159-cycles-six-growth-agent24.md` and the exact local max96 theorem in `results/2026-11-28-raw45-five-hole-exact96-agent24.md` are unaffected. This depth-four survey is a **selection guide** for future source-certificate search, not a completion of the global BB6 proof. Longer simulations, ngram closures and inductive growth theorems should be attempted only on branches not already discharged in the accepted portfolios.
