# Raw10 box15: first-hole partition and symbolic bouncers

## Status
Intermediate result, 2026-11-26. Exact source parent is base34 rectangle index 15, encoded by the existing Agent17 source bridge. This incarnation reconstructed its 12 domains by exact subtraction of the 66 rows:
`[8], 0..24, [11], [6], [17], [13], [11], 0..24, [0,3,4,12,18,20,21,22,23,24], 0..24, 0..24, 0..24`.
Code 0 is halt, -1 unassigned; ordinary code v uses next=(v-1)/4, write=(v-1)/2%2, right=(v-1)%2. Total mass 97,656,250.

## Discovery
First-hole DFS, 256 live steps, exact relative and translated-cycle tests:
| terminal class | leaves | completion mass |
|---|---:|---:|
| relative cycle | 20,722 | 11,889,250 |
| finite halt | 53,862 | 15,543,894 |
| translated cycle | 125,031 | 68,211,375 |
| all ordinary | 1,084,056 | 1,084,056 |
| open | 9,003 | 927,675 |

1,346,536 visited nodes; maximum found ordinary score 257. Two-stack ngram closure widths 1..20, cap 30,000 removes 8,595 open leaves (911,475 mass). Exact replay of the remaining 408 with first-hole splitting to 10,000 live steps yields 116 halting leaves and 2,784 all-ordinary leaves; 292 open, mass 13,300. The largest observed halt has 7,790 live steps, score 7,791, table [8,18,11,6,17,13,11,13,12,24,4,0]. Symmetric ordinary/lag-one RLE saturation resolves 276, leaving 16 one-hole tables; deeper ngram resolves four more, lag 3 and 5 resolve two more. All 16 survived 6,766,859 exact live steps, which is finite evidence only.

## Ten-table final discovery frontier
Indices are zero-based in this report:
```
0  8 21 11 6 17 13 11 19 3 2 15 -1
1  8 19 11 6 17 13 11 21 4 20 -1 11
2  8 19 11 6 17 13 11 23 4 20 -1 10
3  8 20 11 6 17 13 11 21 4 20 -1 11
4  8 20 11 6 17 13 11 23 4 20 -1 10
5  8 4 11 6 17 13 11 19 24 11 3 -1
6  8 4 11 6 17 13 11 19 24 11 4 -1
7  8 10 11 6 17 13 11 19 24 10 4 -1
8  8 12 11 6 17 13 11 19 24 10 4 -1
9  8 24 11 6 17 13 11 19 24 10 4 -1
```
Each has exactly one missing slot, so every ordinary completion is a total no-halt machine; it suffices to decide the ten completions in which the hole is filled with halt.

A local Lean 4.36.0-rc2 proof establishes all-time nonhalting for indices 1,2,3,4,7,8,9, using an explicit primitive two-infinite-ray model and a recurrent B0 section with 6k+1 consecutive ones on the left and blank right. Exact return costs respectively 20k+17,24k+17,16k+15,20k+15,26k+15,30k+19,22k+11. Initial entry times respectively 18,18,16,16,16,20,12 at k=1. All seven axiom profiles are [propext, Quot.sound]. The two finite-word sweep lemmas quantify over arbitrary ray tails, and the recurrence is proved for every natural k. No source-level adapter yet, and the exhaustive discovery partition itself is not yet kernel certified. Do not claim an accepted box15 Cover, exact global score, or change in Canonical58 count. Remaining literal machines: 0,5,6.

## Next proof edge
Preserve the Lean recurrence proof and discovery programs, discharge the remaining three literal tables, then emit/check the complete partition with original source identities and weighted halt bounds. No repeated full singleton-projection scan.

## 2026-11-26 update: nine nonhalting bouncers proved

Indices 5 and 6 also have local kernel proofs, in the same `Bouncers.lean`. For the section B0 with 6N+1 ones on the left and blank right (N≥1), the exact return is to 6(N+2)+1 ones. Costs are 54N+62 and 48N+52 respectively. Blank entry reaches N=2 in 63 and 53 steps. The three-pass sweep proof quantifies over arbitrary tails and uses a commuting-word lemma to compose all three phases. All nine `never1` … `never9` declarations are accepted locally with [propext, Quot.sound]. Index 0 is the only literal machine still undecided in the discovery frontier. The previously found 7,791 finite score is still only an observed lower bound for the box; the proof of all other branches and source ingestion are outstanding.

Agent13 already proved the exact weighted minimal-halt slice reduction in `im-results/agent13-raw10-box15/WeightedBoxMinimalHalt.lean` and the domain identity in `Box15Source.lean`. Reuse them; do not recreate the source-box bridge.
