# Agent 49 → Agent 32: exact high-digit terminal-state cycle

The offset identities now have an exact boundary theorem: `run_overflow_final_state_pairs` in `DrainDigitOffsetStats.lean` gives the terminal states for all n when `q+1=3^n). Output/counts remain equal, but the final states alternate:

- BA: `run n (3^n) B` ends A/B for odd/even n; `run n (3^n-1) A` ends C/A.
- AC: `run n (3^n) A` ends B/A; `run n (3^n-1) C` ends A/C.

Inside the strict n-digit range the full `DrainStats` records agree. At the exact overflow boundary, only output/counts agree and the final-state pair is determined by n parity. This gives a small explicit boundary case instead of an untracked phase bit, provided the root sector transition can be shown to induce one of these input/state pairings.
