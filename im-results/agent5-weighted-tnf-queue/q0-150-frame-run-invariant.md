# q0-150: three nonhalting siblings by a coupled frame/run invariant

**Mathematical proof, source acceptance pending.** These are exact open one-hole leaves of the frozen q0-150 scan 46026792866, not generic prepared-tape experiments. The three tables are

```
1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LA1RB
1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB
1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0RD1RB
```

All have the sole unspecified row E0. The only difference is F0. Write a configuration at E using the left word L (nearest cell first, excluding the scanned cell) and the right word R (nearest cell first, including the scanned cell), ignoring zero padding at the far blank ends.

## Invariant

L is a stack of frames `0^m 11`, each m>=1. Its debt is S = sum(m-1). R is a run of 3n+1+b ones (n>=0, b=0 or1), followed by a list of good runs separated by a single zero, each of length 3a+1 (a>=0), and optionally one last positive multiple-of-three run, again separated by a single zero. Let g count the good runs following the first. Define the right capacity P = g+1-b. Require S<=P.

The actual blank orbit reaches E after seven ordinary steps, L empty and R=1. Hence S=0, P=1.

## Local return equations

All words below are nearest-first. X is an arbitrary untouched right suffix beginning with 1, or empty (followed by blanks). U is the remaining left frame word. When the first run has length >=4, the three assigned moves E1, F1, B1 give
`(L,111R') -> (011L,R')`, where R' begins with 1. This pushes a debt-zero frame and preserves the right capacity.

For shorter first runs, the left action is the same for R=10X and R=110X. The right columns include the scanned E1 symbol; `Z` means the all-blank left tape.

| L | L' | R=10X | R=110X | cost first/second (F0=0LA or 0LD) |
|---|---|---|---|---|
| Z | Z | 110X | 1111X | 11/15 |
| 000V | 00V | 110X | 1111X | 11/15 |
| 011U | 0U | 1010X | 10111X | 8/12 |
| 0011U | 0U | 11110X | 111111X | 13/17 |

Here 000V is a nonempty frame of length at least three zeros (the table also applies to three blank zeros), and U begins with zero or is all blank. In the rows 011U and 0011U, the added zero increments the next frame length if a next frame exists. In the F0=0RD variant, first-column costs are two steps longer when X is nonempty. When X is empty, the F0=0RD first-column outputs instead are 11111, 11111, 101111, 1111111 respectively, with costs 21,21,18,23. Second-column outputs and costs are unchanged. All these are bounded local computations using only assigned transitions; the independent finite-prefix witness generator checks the concrete trace without inspecting an unknown suffix. The source proof should additionally transport through zero padding, since the repository's zipper preserves explicit trailing zeros.

## Closure

If the first run is reduced to length one or two, classify the top left frame:

* No frame: the updated left is blank, S'=0, and the returned R grammar is valid (merging a next good run gives first residue 2; merging a last multiple of three or the blank gives residue 1).
* m=1: the top frame is popped, incrementing the next m if present, so S'<=S+1. If b=0, a new good run is inserted. If b=1, the next run is extended by three (or a terminal multiple-of-three run is created if none existed); the first residue becomes 1. Thus P'=P+1. The special 0RD empty-X branch also inserts one good run.
* m=2: S>=1, and popping the frame and increasing the next gives S'<=S. If b=0, the first run becomes 4 (or 7 in the special blank branch), P unchanged. If b=1, P>=1 forces a next good run; merge 6 with it, so first residue becomes 1, g decreases by one and P unchanged. The potentially unsafe blank or terminal-multiple-of-three merge is excluded by the invariant.
* m>=3: S>=2. Decrement m, S'=S-1. If b=0, first residue changes 1 to 2, P'=P-1 (the special 0RD empty-X case is impossible since then P=1). If b=1, P>=2 forces a next good run; merge 4 with it, first residue stays 2, g decreases by one, P'=P-1.

The right grammar and S'<=P' are preserved in all reachable cases. Every return has positive length and all intermediate moves are assigned. Consequently there are arbitrarily long prefixes of the blank run which never use E0. Every compatible total completion is nonhalting.

This is a genuinely coupled, unbounded invariant, not a finite-step extrapolation. It closes three mathematical cylinders once the finite local equations and source transport are accepted. It does not close q0-150's remaining leaves or BB(6).
