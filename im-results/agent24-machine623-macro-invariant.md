# Machine #623: empirical A-state prefix invariant and macro proof candidate

**Status:** intermediate research only. The observations below are reproducible simulation evidence, not a Lean theorem and not a proof that #623 is nonhalting. The compiled `Machine623HaltCylinder` result still isolates the original #623 machine as the only nontrivial completion; the missing obligation is `NeverHalts machine623`.

## Exact transition table used

States are A–F; each entry is `(write, direction, next)`, with direction `1=R`, `0=L`. A missing entry is halt.

```python
T = [
    [(1,1,1), (0,0,4)],  # A0, A1
    [(0,1,2), (1,1,2)],  # B0, B1
    [(0,1,3), (1,0,0)],  # C0, C1
    [(1,0,3), (0,0,0)],  # D0, D1
    [(1,0,5), (1,0,2)],  # E0, E1
    [None,   (0,0,0)],   # F0, F1
]
```

## Empirical observations

A direct exact-tape replay from blank for 2,000,000 steps did not encounter F/0. Across all A/1 events, the two cells immediately left of the head had these counts:

| left1,left2 | count |
|---|---:|
| 11 | 197,699 |
| 10 | 1,465 |
| 01 | 453 |
| 00 | 0 |

A stronger pattern held at every A-state in a 500,000-step replay. Let `lo` be the minimum head position visited so far, `h` the current head, and `d=h-lo). The finite visited prefix strictly left of the head, `[lo,h-1]`, had no adjacent `00`; whenever `d>0), its first cell `lo` was 1.

The following additional boundary conditions also held in that replay:

1. `d=0`: state A reads 0, and cells `h+1,h+2,h+3` are not `100`.
2. `d=1`: if A reads 1 then cell `h-1` is 1; if A reads 0 then cells `h+1,h+2,h+3` are not `000`.
3. `d=3` and A reads 1: cell `h-2` is 0.

The replay saw 149,538 A-state visits in the 500,000-step window. These claims should be independently reproduced before being used as proof premises.

## Candidate invariant

At every A configuration, with `lo` the visited left frontier:

- if `d=0), then the current bit is 0 and the right three-bit word is not 100;
- if `d>0), then `tape(lo)=1` and the finite word `tape[lo..h-1]` contains no adjacent 00;
- if `d=1), A/1 has left neighbor 1, while A/0 has right three-bit word different from 000;
- if `d=3) and A/1, then the second-left bit is 0.

The prefix condition plus the boundary clauses exclude A/1 with two zeros immediately left, hence exclude the direct E/0 → F/0 halt. The additional A/0 clauses are needed to preserve the invariant through the D sweep when the next A head returns to the left frontier.

## Macro transition analysis

Let an A configuration have head at (x).

### A/0 branch

A writes 1 at (x), B preserves the bit at (x+1), then C either:

- reads 1 at (x+2) and returns to A at (x+1); the new left prefix is the old prefix with a 1 appended;
- reads 0 and enters D at (x+3). D scans left, writing 1 on zeros, and cannot pass the 1 just written at (x). It returns to A at:
  - (x+2), if D reads 1 immediately at (x+3); the new left prefix appends (1,b);
  - (x), if D passes the zeros at (x+3,x+2) and reads 1 at (x+1); this can be dangerous only at (d=0), where the forbidden right pattern is 100;
  - (x-1), if it also passes the zero at (x+1) and reads the A-written 1 at (x); this can be dangerous only at (d=1), where the forbidden right pattern is 000.

In the non-boundary cases, the new left prefix is unchanged, extended by a 1 (possibly followed by one bit), or truncated; the no-00 condition is preserved.

### A/1 branch

A writes 0 and moves left to E at (x-1).

- If (x-1=1), E/1 moves left to C at (x-2). C/1 returns A at (x-3); C/0 moves right to D at (x-1), where D/1 returns A at (x-2) with current bit 0.
- If (x-1=0), E/0 moves left to F at (x-2). F/1 returns A at (x-3); F/0 halts. The no-00 prefix and the (d=0,1) boundary clauses are intended to exclude this last case.
- If a return at (x-3) would land exactly at the old left frontier with bit 1, the (d=3), A/1 boundary clause forces the safe context 10; for (d<3), the new head is a fresh blank frontier, and for (d>3), the new prefix is a truncation.

This analysis is a proof plan, not a completed formal argument. In particular, each boundary case and the preservation of the frontier witness must be proved from the exact transition semantics.

## Finite-window abstraction experiment

A sound over-approximation used a seven-cell window ([h-3,ldots,h+3]), with distances to visited frontiers capped at 4. When a capped distance is decremented toward its frontier, the abstract transition branches to both 3 and 4; this nondeterminism is essential for soundness.

The BFS reaches 1,815 abstract states and excludes the pattern:

- state A;
- current bit 0;
- left neighbor 0;
- right three bits 100.

This supports the (d=0) / A/0 boundary clause. It does **not** exclude A/1 with left bits 00: the abstraction forgets correlations in the longer left prefix and admits spurious states. The earlier version that decremented a saturated distance as though it were exactly 4 was unsound and must not be reused.

## Retracted false lead

A previous check incorrectly suggested that the visited suffix right of the head also had no adjacent 00 at A-states. This is false: at step 23 (zero-indexed), state A has head (-3), and cells (-2,-1) are both 0. Only the left-prefix observation remains.

## Recommended next step

Formalize the A-state macro invariant with an explicit finite visited tape (for example, a list of bits with the head index and left/right frontier). Prove the A/0 and A/1 macro cases, including the (d=0,1,3) boundaries, then derive `NeverHalts machine623`. Do not promote this file to `results/` unless and until the invariant and the source-level simulation are fully proved.
