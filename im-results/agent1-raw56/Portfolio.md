# E1=0RC complete candidate portfolio (2026-11-27)

All sixteen C1 choices remaining after the three source-accepted child theorems (1RD, 0RD, 1LE) have a complete **candidate** partition. This is not yet a kernel-accepted parent bound. The fixed cap=1000, lookback=32, depth=6 cut and FAR5 bank are pinned by SHA-256 per choice; the supplemental FAR6 strings, late terminal queries/cycles and symmetric BiDFA parameters are in `rc_portfolio.tsv`.

| C1 | Opens | FAR5 | FAR6 | BiDFA | Late |
|---|---:|---:|---:|---:|---:|
| 0LA | 739 | 719 | 1 | 19 | 0 |
| 0LB | 354 | 318 | 0 | 36 | 0 |
| 0LE | 473 | 448 | 0 | 22 | 3 |
| 0LF | 1588 | 1507 | 0 | 80 | 1 |
| 0RA | 262 | 251 | 0 | 11 | 0 |
| 0RB | 781 | 762 | 0 | 19 | 0 |
| 0RE | 323 | 297 | 0 | 26 | 0 |
| 0RF | 657 | 636 | 0 | 21 | 0 |
| 1LA | 874 | 843 | 0 | 31 | 0 |
| 1LB | 465 | 450 | 1 | 14 | 0 |
| 1LC | 411 | 405 | 1 | 5 | 0 |
| 1LF | 1334 | 1295 | 0 | 39 | 0 |
| 1RA | 431 | 407 | 4 | 20 | 0 |
| 1RB | 499 | 474 | 0 | 25 | 0 |
| 1RE | 727 | 710 | 3 | 13 | 1 |
| 1RF | 1124 | 1084 | 1 | 39 | 0 |

The candidate search combines Agent25's ordinary n-gram, run-length and block-periodic abstraction with Agent19's lag-XOR idea (retain a k-bit shift register and run-length abstraction of the XOR differences). All use the same original-source FastBiDFA checker; the discovery code is untrusted. Search for smaller witnesses across this portfolio substantially reduces proof checking cost, e.g. aggregate states 40184 to 8564 for 0RE before retaining already accepted individual witnesses.

Important: 0LF leaf 907 is `1RB1RE_1RC---_0RD0LF_1LD1LE_1RA0RC_1LC1LF` and first queries B1 at step 9474. The old weighted bound 7014 cannot hold for this branch (choose Halt at that slot). Its regenerated proof is at bound 10000; the remaining fifteen branches stay at 7014. Overall composition must transport the smaller bounds monotonically to 10000. The other late cases are 0LE M21, M208, M404 (last queries at 1087,1003,1944), and 1RE M427 (translated cycle from 307 with period 834).

## Reproduction

Run `python im-results/agent1-raw56/prepare_rc_portfolio.py OUT [C1 choices...]`. Omit the optional choices for all sixteen. Requires g++, node, Python; the script pins source blobs and cut/open/FAR5 bytes, checks every replayed state and edge count, and asserts a disjoint exhaustive partition of the open indices. The generated `OUT/<choice>gen/manifest.json` lists module dependencies. Compile against source-accepted artifact 15160313745 and the exact Agent32 `FastBiDFA.lean` (checked locally with Lean 4.36.0-rc2), then compile each manifest. The mathematical result is established only by successful canonical checker/consumer source compilation and standard-axiom audit.

Parameter encoding: n=ordinary window width; r=number of runs,c0,c1,m0,m1; l=lag,number of runs,c0,c1,m0,m1; b=window,threshold,modulus,period list. BiDFA fields are index:parameters:states:edges. FAR6 fields index:certificate code. Late fields index:kind,arguments. Original raw tree/open/FAR5 hashes are independent of generated proof bytes.
