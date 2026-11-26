# Raw139 E0=1RD — candidate census and two hard leaves

This is the normalized depth-2 sibling with move `⟨true,true,3⟩` of `BB6.Agent6Raw139Normalized.remainingRows`: `1RB---_1RC---_1LD---_---0LE_1RD1RC_------` (codes `[7,24,11,24,14,24,24,16,15,11,24,24]`). It has six holes. **No parent Cover has yet been accepted.**

## Candidate partition

`reproduce.py` applies the existing Agent6/48 search mechanism (C++ exact bounded prefix, ordinary-move splits, candidate side cycles, small FAR, then block-FAR). Its 250-step first pass gives 26,980 splits and 620,541 leaves: 429,405 side cycles, 128,403 last-hole queries, 55,075 FAR witnesses and 7,658 initially open leaves. The second pass gives 7,592 block-FAR candidates, 54 late queries, 10 cycles and two unresolved leaves. One late query has two holes; its 24 ordinary children yield 22 block-FAR and two late last-hole candidates. Every halt-at-split case remains part of the future weighted audit. Counts and checksums are candidate-search evidence, not trusted certificates.

The two remaining tables, each with only F0 unspecified, are:

- 2959: `1RB1LB_1RC1LF_1LD1RE_1LA0LE_1RD1RC_---0LA`; direct simulation hits F0 at step 94,323,044.
- 4267: `1RB0LC_1RC1RA_1LD0RB_1LF0LE_1RD1RC_---0LA`; direct simulation through 100 million steps did not query F0. No nonhalting proof follows.

## Compact recurrence for 2959

Use a B section with an empty left stack (scanned blank) and right stack `1^n`. Blank entry is at step 10 with n=4. Direct symbolic inspection suggests:

- Even n: return with n+3 ones in 4n+6 steps.
- Odd n: in n+3 steps enter A with n+2 ones on its left and a single one on its right. Each group of three left ones converts into right block 011 in three steps. Write n+2=3k+r. For r=2, two further steps query F0, with empty left and right 11(011)^k1. For r=1, one step gives B with right 1(011)^k1. For r=0 and k≥2, 18 steps give B with right 1^8(011)^(k−2)1.
- B with right 1^m(011)^k1, k>0, returns with right 1^(m+5)(011)^(k−1)1 in 4m+6+6(m mod 2) steps.

The recurrence reproduces the direct query count with final odd n=12,285 and k=4,095. The next task is to prove the symbolic word transfers for arbitrary parameters using SweepPumping and connect to the actual weighted first-hole bound. The remaining machine 4267 needs an all-time invariant or a terminal query; a longer finite run is not a closure proof.
