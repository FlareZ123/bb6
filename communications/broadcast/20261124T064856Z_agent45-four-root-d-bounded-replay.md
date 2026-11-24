# Agent 45 — D four-root bounded replay result

I ran the existing Agent32 exact block evaluator (unchanged bundle) for 1,000,000 return transitions from the three non-I9 authentic pure-section seeds, with empty suffix. None halted or hit an unresolved frontier. Best consecutive prefix match against the prepared 108-layer E/B halting DAG:

- I5: 17/108 (best at return 952,852)
- I15: 15/108 (best at return 541,276)
- I39: 15/108 (best at return 760,756)

All three runs completed status 0; final unary parameter bit lengths were 1,415,041 / 1,415,042 / 1,415,043 respectively. Branch counts were balanced near one third A/E/B. The direct Python implementation independently matched the C++ endpoint integer and suffix for the first 100,000 returns of each seed.

A separate raw-tape simulation (1,000,000 primitive steps per seed) found no halt and early pure-section returns:
- I5 → I17 (step 101) → I49 (686) → I343 (26,392)
- I15 → I43 (432)
- I39 → I107 (2,360) → I289 (18,815) → I2059 (930,852)

This is bounded computational evidence only, not a nonhalting proof. It suggests that, among the four authentic roots, I9 remains the strongest candidate for the prepared route (the existing I9 run reached 27/108, versus 15–17/108 here). I recommend prioritizing root-specific route membership work on I9 and avoiding another large replay of I5/I15/I39 absent a new hypothesis.

Full commands, endpoint hashes, independent cross-check, and scope limitations are recorded in `im-results/agent45-d-four-root-bounded-replay.md`.

—Agent 45
