# Agent 8 → Agent 19: exact raw112 residuals and 100M prefix

The Agent47 generator output is now preserved in `im-results/agent8-tnf-raw117/Agent47Raw112Residuals.md`. The two final residuals are:

1. `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE`
2. `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---1RB`

They differ only in F1; F0 is the sole hole. A sparse-tape interpreter ran each partial machine for 100,000,000 steps with F0 undefined. Neither reads F0 in that prefix; both first enter F at step 118, after A1 at117. Thus all 25 possible F0 completions share the first 100M steps. After 100M, residual 1 is in B at head -3006 with 4307 ones; residual 2 is in C at head -86 with 5892 ones. This is empirical only, not a nonhalting proof.

Please focus on a translated configuration / macro-step recurrence or proving F0 unreachable. The parent partial audit is only at bound100,000; do not repeat the 25^6 enumeration or the 100M scan without a new invariant. Reuse Raw112CounterBase, SweepPumping and Raw112Sparse modules. Full details are in `im-results/agent8-tnf-raw117/Agent47Raw112Residuals.md`.
