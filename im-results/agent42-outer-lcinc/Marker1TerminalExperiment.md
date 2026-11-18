# Marker-1 terminal behavior: finite exact-table experiment

**Status:** exploratory computation only. This is not a proof of halting or nonhalting, and no claim about BB(6) follows.

## Configuration being tested

The simulator starts the original six-state, two-symbol machine in state 3 at head 0, with the exact S0 physical tape

```
s0Config (markerWord marker ++ d0 ++ d1pow L ++ lh) A 0 0 0
```

where `A,L ≥ 1`, `binDec A 0 = d1pow A`, `binDec L 0 = d1pow L`, and the right-facing word is

```
s0RightFacing 0 = [0,1,1,1,0,0] ++ d1pow 1
```

The marker-0 control is the already-proved terminal interface. The marker-1 case is the context arising from the m=2,n=1 reset endpoint: `l = markerWord 1 ++ d0 ++ binDec L 0 ++ lh`.

The simulator transcribes the 12 transitions of the original `tm2` table in `ChampionRootBridge.lean`. It uses a finite set of 1-cells and treats every unlisted cell as 0. A reported halt at step `s` means `s` successful transitions occurred and the next transition query is undefined.

## Reproduction

```sh
node marker1_terminal_experiment.cjs 1 2 4 1000000
node marker1_terminal_experiment.cjs 0 2 4 1000000
node marker1_terminal_experiment.cjs --grid 1000000
```

The first argument is the marker (0 or 1), followed by A, L, and the step horizon. The grid mode tests markers 0 and 1 for 1≤A≤5 and 1≤L≤6.

## Observed data

The marker-0 controls reproduce the exact terminal theorem count

[
59+12(A+L).
]

For marker 1, the following cases halted within the stated horizons:

| A | L | Successful steps |
|---:|---:|---:|
| 1 | 2 | 11,319 |
| 2 | 2 | 40,521 |
| 3 | 2 | 152,913 |
| 4 | 2 | 593,685 |
| 5 | 2 | 2,339,217 |
| 1 | 4 | 168,111 |
| 2 | 4 | 653,601 |
| 3 | 4 | 2,577,129 |
| 4 | 4 | 10,234,413 |
| 1 | 6 | 2,638,407 |
| 2 | 6 | 10,478,649 |

The following odd-L cases survived the full listed horizon; this is not a nonhalting proof:

| A | L | Horizon |
|---:|---:|---:|
| 1 | 1 | 1,000,000 |
| 2 | 1 | 1,000,000 |
| 3 | 1 | 1,000,000 |
| 4 | 1 | 1,000,000 |
| 5 | 1 | 1,000,000 |
| 1 | 3 | 10,000,000 |
| 2 | 3 | 10,000,000 |
| 1 | 5 | 10,000,000 |
| 2 | 5 | 10,000,000 |
| 3 | 3 | 1,000,000 |
| 4 | 3 | 1,000,000 |
| 5 | 3 | 1,000,000 |

The even-L halting times grow by factors approaching 4 per increment of A and 16 per increment of L by 2. This is an empirical pattern, not a fitted theorem. It suggests a nested counter-like terminal macro. The odd-L runs show slow rightward drift and growing support at the tested horizons, but no all-time conclusion is justified.

## Research questions

1. Is there a quantified macro theorem for marker 1 and even L, with a recurrence explaining the observed growth?
2. Does marker 1 with odd L enter a translating cycle or an infinite expanding orbit?
3. Can the marker-1 root endpoint from the m=2,n=1 branch be classified using such a theorem? In particular, the authentic middle-34 root has L=3 in the current wrapper, so the odd-L case is the relevant one.
4. Is there a simple invariant or quotient that proves nonhalting for odd L without simulating the full expanding tape?

## Evidence boundary

The marker-0 control is a useful check that the transcribed transition table and physical tape orientation agree with the existing terminal theorem. The marker-1 observations are still finite computational evidence. The script does not replace a Lean proof, a cycle certificate, or a quantified simulation theorem.


## State-4 exit observation

The transition table has a useful exact reduction:

- The only undefined transition is state 0 reading 1.
- The only way to enter state 0 is from state 4 reading 0 (which writes 1, moves right, and enters state 0).
- Therefore a halt occurs exactly when a state-4 scan reaches a 0 whose immediate right neighbor is 1; the following state-0 query then reads 1.

The simulator now counts these events. Observed samples:

| Marker | A | L | State-4 on 0 | Next cell 0 | Next cell 1 | State-0 reads 1 |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 3 | 5,289 | 5,289 | 0 | 0 |
| 1 | 2 | 3 | 4,453 | 4,453 | 0 | 0 |
| 1 | 1 | 2 | 157 | 156 | 1 | 1 |
| 1 | 1 | 4 | 637 | 636 | 1 | 1 |
| 0 | 1 | 3 | 5 | 4 | 1 | 1 |

This isolates a sharper conjecture than parity-dependent survival:

```
marker=1 and L odd:
  every reachable state-4 configuration reading 0 has a 0 immediately to its right.
```

If proved, this invariant immediately implies nonhalting for all A and odd L. The even-L samples instead eventually produce one state-4/0/1 boundary, causing the unique halt query.

The transition-level equivalence is proved directly from the table; the quantified odd-L invariant is **not** proved. The event counts are finite computational evidence only.
