# Raw140: candidate doubling return map for the last two siblings
Status: **exact finite computations and a conjectured general recurrence, not a nonhalting certificate**. Distinct from the 19 restricted-attractor entries. Local 3-hole partition IDs 73 and 80; these both use A1=1RF, F1 undefined, and F0=0LB or 0RD respectively. Literal tables:
- 1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LB---
- 1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---

Use little-endian three-cell blocks with nearest boundary first; BR means B entering a block at its left boundary. Write T(m,n,s)=BR(5^m,(644)^n s). Both blank runs enter T(32,1,64) at primitive time 5985 (1176 macro steps after time 2). Observed first five returns:

| F0 | (m,n,s) | primitive cost |
|---|---|---:|
| 0LB | (78,5,62) | 36148 |
| | (170,16,6421) | 198986 |
| | (354,43,6221) | 961920 |
| | (722,100,62542) | 4292086 |
| | (1458,219,6405) | 18271014 |
| 0RD | (80,5,6221) | 38444 |
| | (176,17,6421) | 215514 |
| | (368,45,6405) | 1047238 |
| | (752,105,62542) | 4677608 |
| | (1520,230,62) | 19911584 |

Candidate general law for even m>=18, n>=1: let p=m for 0LB and p=m+2 for 0RD. Set m'=m+p+14, n'=n+floor(p/6)+offset. Offset and new suffix below, columns p mod 6 = 0,2,4.

| s | 0 | 2 | 4 |
|---|---|---|---|
|64|-2,6405|-1,62|-1,6221|
|62|-2,6421|-2,62542|-1,64|
|6421|-1,62|-1,6221|-1,6405|
|6221|-2,62542|-1,64|-1,6421|
|62542|-1,6221|-1,6405|0,62|
|6405|-1,64|-1,6421|-1,62542|

Each of the 120 tested m/s/f combinations (m=18,20,...,36,n=2), and five genuine return intervals per table, agrees. This is an inductive candidate invariant with strictly positive return times and no F1 access; if proved, closes both 25-completion cylinders. Do not infer nonhalting merely from finite runs.

Proof route: initial reset uses BR6->FR5, FR4->BL4, BL5->DL2 (0LB) or BR6->FR5, FR4->FR5 twice, FR6->BL6, BL5->DL2 (0RD). Common DL(5^p,2W) -> CR(6^(p+2)4,W) costs 12p+16 via homogeneous sweeps. For 0LB W=44(644)^(n-1)s; for 0RD W=(644)^(n-1)s. Subsequent long sweeps are shared. A first-era section D(k,j,n,s)=DL(6^k4,4^j64(644)^n s) trades one unit of k for one unit of j while rotating a finite suffix. The second era starts near DL([],4^a 6 4^b 64(644)^n s), moving four 4 blocks to the first run and removing two from the second. Derive universal micro-transducer laws by symbolic arbitrary-stack contexts and induction, rather than longer simulation. Reproducer Raw140DoubleGrowth.js. No Lean checked claim here.
