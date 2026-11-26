# Raw10 base34 rectangle 15: independent discovery closure and symbolic nonhalting

**Status (2026-11-26):** all 97,656,250 completions are computationally classified by first-hole enumeration and sound-in-principle certificate methods. Nine final one-hole cylinders have standalone Lean 4.36.0-rc2 proofs of all-time nonhalting, with [propext, Quot.sound]. The tenth has a successful finite forward block-FAR discovery certificate; its Lean/source audit is pending. The largest discovered ordinary and weighted halt score is 7791, and a source lower-bound witness has been emitted. Neither the full rectangle upper bound nor any reduction of the Canonical58 roster has yet been source-accepted.

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

Table [8,18,11,6,17,13,11,13,12,24,4,0] halts after 7790 live moves, plus the halt, giving 7791. Its zero-write transition graph has no incoming path to A, so weighted score is also 7791. All other discovered finite leaves have weighted score at most 1946 (or at most 262 among initial short leaves). [Lower.lean](Lower.lean) supplies the source lower theorem pending audit.

## Source certification and next edge

- [BouncersSource.lean](BouncersSource.lean) uses pointwise ray semantics and exact source table equality to transfer nine local proofs. Initial run [45907932897](https://github.com/FlareZ123/bb6/actions/runs/45907932897) failed at ray extensionality; the repair is in d83c8eda. Ten-case source audit [45908327095](https://github.com/FlareZ123/bb6/actions/runs/45908327095) is pending.
- Agent13's existing [Box15Source](../agent13-raw10-box15/Box15Source.lean) and [WeightedBoxMinimalHalt](../agent13-raw10-box15/WeightedBoxMinimalHalt.lean) prove the exact domain and weighted minimal-halt reduction.
- Agent49's earlier [five-family proof archive](../agent49-raw10-box-family/README.md) already emits the entire partition. Reuse it instead of duplicating millions of first-hole leaves. Isolated B1-code-6 (base34 rectangle15) audit [45908080080](https://github.com/FlareZ123/bb6/actions/runs/45908080080) is pending; its emitted source theorem must be accepted before integrating the rectangle into Raw10RefinedCut.
