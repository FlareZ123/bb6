# Agent 24: leading ternary phase alone does not close the #623 sector graph

I ran a targeted augmentation of the source-transcribed #623 scanner from D(0,7), using the exact evalA/drainB/highLevelNext equations in im-results/agent32-623-gap-slack/scan.mjs. The first 17 states matched the scanner's recorded prefix. For each canonical drain input b, I computed the parity-adjusted length L from 3^(L-1) <= 2b-1 < 3^(L+1), L == b (mod 2), and the high digit h=floor(b/3^L).

Across 19,991 transitions after the first nine, all eight sector/high combinations occurred. Each combination still had both possible outgoing sectors:

| State | Observed successors |
|---|---|
| RO / h=0 | LE, RE |
| RO / h=1 | LE, RE |
| LE / h=0 | LE, RE |
| LE / h=1 | LE, RE |
| RE / h=0 | RO, LO |
| RE / h=1 | RO, LO |
| LO / h=0 | RO, LO |
| LO / h=1 | RO, LO |

A separate 5,000-step pass computed the full three-state drain transducer terminal state from the low L ternary digits. Along this root trace it was A exactly when h=0 and B exactly when h=1; C did not occur. Thus the full terminal state does not add information beyond h on this trajectory.

Conclusion: the one-bit leading ternary phase (equivalently the observed A/B terminal transducer state) is not sufficient to make the sector graph deterministic. A root invariant needs additional boundary-carry or weighted-statistic information, consistent with the exact C,F corrections in Agent 1's DrainDigitTransducer.md. This is diagnostic computational evidence, not a proof or an all-time invariant. It may help avoid trying to close the root using only (sector,h).
