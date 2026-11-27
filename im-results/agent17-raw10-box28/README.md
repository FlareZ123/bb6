# Raw10 original rectangle 28: D0=14, D1=17/18

Agent17, 2026-11-27. New work, not the prior Box15 family.

The exact parent has A0=8, B0=11, C0=11, C1=13 and D0 in the original source residual set. Fix D0=14 and D1=17 or 18. The two disjoint cylinders each contain 25^6 = 244,140,625 completions. The source weighted one-halt reduction restricts each to six slices with 24^5 = 7,962,624 representatives apiece. Discovery artifacts [run 45920307876](https://github.com/FlareZ123/bb6/actions/runs/45920307876) cover 47,775,744 normalized representatives per branch; classification uses exact first-hole partition, concrete halts, translated cycles, n-gram and stack certificates.

| D1 | largest discovered ordinary score | unresolved normalized leaves | artifact |
|---|---:|---:|---|
| 17 | 534 | 3 | [15164081777](https://github.com/FlareZ123/bb6/actions/runs/45920307876/artifacts/15164081777) |
| 18 | 110 | 0 | [15163683060](https://github.com/FlareZ123/bb6/actions/runs/45920307876/artifacts/15163683060) |

The 534 witness is [8,18,11,4,11,13,14,17,24,17,6,0].
Discovery alone is not a source Cover.

## Three D1=17 residual machines: explicit recurrent solutions

Rows use code 0=halt, 1+4q+2write+direction (right=1). List order A0,A1,B0,B1,...,F0,F1.

The first two rows are
[8,0,11,24,11,13,14,17,22,9,19,4] and
[8,0,11,24,11,13,14,17,22,17,19,4].
After six live moves each reaches E scanning zero with an all-zero tape. Define a root configuration with state E, left blank, scanned zero, right marker zero followed by blocks (0,b,c), b,c least-significant-first digit bits. The four-step root opening reaches A at the first guard with one left marker. Each maximal low-order digit 3 is crossed in three moves, writing three ones. The next digit 0/2 is incremented by a four-move local update, followed by 3k clearing moves for k carried digits; digit 1 is incremented by a three-move update and 3(k+1) clearing moves. Both E1 alternatives clear the required triples. The result is the root with the base-four integer increased by one. The omitted high digits are implicit zeros. This finite positive recurrence establishes nonhalting, with total cost 8+6k for even stopping digits and 10+6k for digit 1. Lean candidate: Box28Base4.lean.

Third row [8,14,11,24,11,13,14,17,3,15,4,0]. After 28 moves it reaches A scanning blank, right blank, left nearest-first 1110111. Define R(k) with left 1^(6k+3) 0 111, scanned/right blank. An exact macro decomposition gives R(k) -> R(k+1) in 43+16k moves. Four moves enter E, 6k moves traverse k*3 pairs of ones, three moves cross the separator, nine moves clear the three remaining left ones, 18 moves turn around, then 10k+9 moves build the longer left block. No F1 is visited. Lean candidate: Box28Sweep.lean. Box28HardSource.lean transfers the local stream arguments to the exact Frontier source machines. Source compilation of these three proofs is still pending.

## Source closure

emit.py consumes the preserved artifacts (not a repeated discovery scan). It generates exact weighted one-halt source domain equations, stack bank, complete first-hole tree and sourceBound at the deliberately conservative bound 3640. Its hard bank must match the three above exact rows. Source jobs use weighted-tnf-raw10-box28-d18-source and -d17-source. The two E/F-swapped branches D1=21/22 should subsequently follow by exact state-renaming invariance, not new discovery.

Do not subtract these rectangles from the global roster until source Cover and integration succeed. Neither the exact score of either full rectangle nor a complete Box28 bound is claimed by discovery.
