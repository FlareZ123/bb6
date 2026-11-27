# Raw10 base34 rectangle 15: independent discovery closure and symbolic nonhalting

**Status (2026-11-27):** the discovery partition covers all 97,656,250 completions computationally. The ten final one-hole cylinders now have original-source all-time nonhalting proofs, accepted in [45908327095](https://github.com/FlareZ123/bb6/actions/runs/45908327095), with only standard axioms. The largest discovered ordinary and weighted halt score is 7791; the lower-bound witness and exact incoming delay graph are now independently source-certified in [45920219572](https://github.com/FlareZ123/bb6/actions/runs/45920219572). The entire rectangle upper bound remains unaccepted: the Family6 partition audit was interrupted after compiling its common external witness bank. The next edge is to finish the existing exact partition proof with durable sharded cuts, not another search or a fresh full monolithic compilation. No global roster reduction follows yet.

## Domain and discovery partition

The existing Agent17 encoded source bridge identifies base34 rectangle index 15. Its 12 domains are
`[8], 0..24, [11], [6], [17], [13], [11], 0..24, [0,3,4,12,18,20,21,22,23,24], 0..24, 0..24, 0..24`.
Code 0 is halt, -1 unassigned; ordinary code v uses next=(v-1)/4, write=(v-1)/2%2, right=(v-1)%2.

First-hole DFS, 256 live steps, exact relative and translated-cycle tests:
| terminal class | leaves | completion mass |
|---|---:|---:|
| relative cycle | 20,722 | 11,889,250 |
| finite halt | 53,862 | 15,543,894 |
| translated cycle | 125,031 | 68,211,375 |
| all ordinary | 1,084,056 | 1,084,056 |
| open | 9,003 | 927,675 |

1,346,536 nodes visited. Two-stack ngram closure widths 1..20, cap 30,000 removes 8,595 open leaves (911,475 mass). Exact replay of remaining 408 with first-hole splitting to 10,000 live steps yields 116 halting leaves and 2,784 all-ordinary leaves; 292 open, mass 13,300. Symmetric ordinary/lag-one RLE saturation resolves 276, leaving 16 one-hole tables; deeper ngram resolves four more, lag 3 and 5 resolve two more. All 16 survived 6,766,859 exact live steps, finite evidence only. The final ten cylinders are below.

## Final cylinders and mathematical certificates

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

Each has one missing slot. A forever-defined partial execution implies nonhalting for every completion, including the halt child.

[Bouncers.lean](Bouncers.lean) establishes a B0 section with 6k+1 consecutive ones on the left and blank right. For indices 1,2,3,4,7,8,9, the exact return is k→k+1, with costs 20k+17,24k+17,16k+15,20k+15,26k+15,30k+19,22k+11 respectively. Initial entry times are 18,18,16,16,16,20,12 at k=1. The finite-word sweep lemmas quantify over arbitrary ray tails.

Indices 5,6 have a three-pass sweep, return N→N+2 for section B0 with 6N+1 ones (N≥1). Exact costs 54N+62 and 48N+52; blank entry to N=2 in 63 and 53 steps. Commuting-word and sweep lemmas compose all three phases. All nine never declarations locally kernel-checked.

For index 0 (`1RB0LF_1LC0RB_0LE0LD_1LC1LE_1LA0RA_1LD---`), mirrored width4 macro blocks with six-block left suffix give forward FAR saturation: 312 left states, 793 right nodes, 1168 edges before minimization. [prepare_hard.py](prepare_hard.py) regenerates using Agent13's generator; [HardSource.lean](HardSource.lean) bridges the certificate to original source semantics.

## Finite maximum witness

Table [8,18,11,6,17,13,11,13,12,24,4,0] halts after 7790 live moves, plus the halt, giving 7791. Its zero-write transition graph has no incoming path to A, so weighted score is also 7791. All other discovered finite leaves have weighted score at most 1946 (or at most 262 among initial short leaves). [Lower.lean](Lower.lean) supplies the source lower theorem accepted in run 45920219572.

## Exact incoming blank-delay graph

The six zero-symbol rows have fixed codes A0=8, B0=11, C0=17, D0=11, E0 in {0,3,4,12,18,20,21,22,23,24}, and F0 arbitrary. The only possible incoming zero-write edge to A is F0=1 or 2. The only possible incoming zero-write edge to F among the other states is E0=21 or 22, and C0 then supplies C→E. A, B and D write one. Consequently the exact possible incoming delays to A are:

- F0 not in {1,2}: {0};
- F0 in {1,2}, E0 not in {21,22}: {0,1};
- F0 in {1,2}, E0 in {21,22}: {0,1,2,3}.

A zero-write directed path must end at A; the graph above exhausts such paths. An independent executable enumeration of all 250 E0/F0 pairs gives 230, 16 and 4 cases respectively. Thus the generic five-move delay allowance can be replaced with an exact per-table allowance of 0, 1 or 3, and every ordinary finite score plus that allowance equals the weighted score. The 7791 witness uses F0=4 and therefore has zero allowance. This does not prove the upper bound on the ordinary score of all completions.

[Delay.lean](Delay.lean) expresses the source-level graph calculation, exact weighted equivalence, and the ordinary-to-weighted bound with at most three additional moves. Initial run [45919670076](https://github.com/FlareZ123/bb6/actions/runs/45919670076) found a single invalid Nat.le.trans field notation, fixed in dc4a9036. The generalized five-sibling source audit, including Lower.lean, [45920219572](https://github.com/FlareZ123/bb6/actions/runs/45920219572) succeeded. The exact graph theorem applies to original rectangles 12, 13, 14, 15 and 25.

## Source certification and next edge

- [BouncersSource.lean](BouncersSource.lean) uses pointwise ray semantics and exact source table equality to transfer nine local proofs. Initial run [45907932897](https://github.com/FlareZ123/bb6/actions/runs/45907932897) failed at ray extensionality; the repair is in d83c8eda. Ten-case source audit [45908327095](https://github.com/FlareZ123/bb6/actions/runs/45908327095) passed: `row_never`, `row_weighted`, `source_never`, and `weighted` report standard axioms only. Its snapshot compiled four roots and did not include the later `Lower.lean`.
- Agent13's existing [Box15Source](../agent13-raw10-box15/Box15Source.lean) and [WeightedBoxMinimalHalt](../agent13-raw10-box15/WeightedBoxMinimalHalt.lean) prove the exact domain and weighted minimal-halt reduction.
- Agent49's earlier [five-family proof archive](../agent49-raw10-box-family/README.md) already emits the entire partition. Reuse it instead of duplicating millions of first-hole leaves. Isolated B1-code-6 audit [45908080080](https://github.com/FlareZ123/bb6/actions/runs/45908080080), job 140209580120, failed with runner shutdown / exit 143 while compiling `Family6R_20_22`, after `Family6External` and many exact partition submodules had compiled. No Lean source diagnostic was observed in the failure tail. The existing manual workflow now has `weighted-tnf-raw10-family6-sharded`, using [family6_shards.py](family6_shards.py): one common proof cut, ten size-balanced partition-module cuts, then an exact manifest-checked `Family6Source` linker and named axiom gate. The driver is untested locally because both shell and Python tools returned `ClientError`. Sharded run [45919377429](https://github.com/FlareZ123/bb6/actions/runs/45919377429) is in progress. The emitted source theorem must actually pass before integrating the rectangle into Raw10RefinedCut. Successful shard artifacts remain reusable if another runner is interrupted.
