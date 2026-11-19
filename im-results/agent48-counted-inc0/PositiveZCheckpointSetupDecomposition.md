# Positive-z first-checkpoint setup: exact sweep/bridge decomposition

**Status:** new finite-trace decomposition of the missing setup macro. The component sweeps already have generic source-level theorem interfaces; the fixed bridges below are finite traces suitable for lifting with `q4BridgeAt`. The global pointwise tape hypotheses and final encoder identity have not yet been formalized, so this is still intermediate work.

## Target

Let
```
ell0 = markerWord 1 ++ d0 ++ d1pow L ++ lh
ell1 = 11 ++ (010)^(A+1) ++ 011 ++ 110
       ++ (010)^L ++ 011 ++ 101 ++ 11
```
The setup macro to prove is
```
s0Config ell0 A 0 z 0
  --(12*(A+L)+3*z+97)-->
s0Config ell1 z (2^z-1) 0 (3*z+5).
```
This is stage 2 of the four-stage first-checkpoint decomposition in
`PositiveZCheckpointNormalForm.md`, not the post-checkpoint first-cycle drain.

## Composition found from the original TM2 trace

After the first counted drain, the source configuration is
`s0Config ell0 A 0 z 0`. The run factors as follows:

1. `state3_left_ones_scan (3*A+1)`: cost `9*A+3`, head moves from 0 to `-(3*A+1)`.
2. Fixed 8-step bridge `B8`: head displacement `-2`.
3. `state3_left_ones_scan (3*L+5)`: cost `9*L+15`.
4. Fixed 20-step bridge `B20`: head displacement `+4`.
5. `counted_right_sweep (L+1)`: cost `3*(L+1)`, head displacement `+3*(L+1)`.
6. Fixed 9-step bridge `B9`: head displacement `+3`.
7. `counted_right_sweep (A+1)`: cost `3*(A+1)`, head displacement `+3*(A+1)`.
8. Fixed 6-step bridge `B6`: head displacement `+4`.
9. `counted_right_sweep z`: cost `3*z`, head displacement `+3*z`.
10. Fixed 30-step bridge `B30`: head displacement `-4`.

The three right sweeps are instances of the existing theorem
`BB6Coverage.Agent48Champion.counted_right_sweep` in
`im-results/agent24-champion-time/CountedSweep.lean`. Each sweep consumes
one consecutive triple of ones per block and advances the head by three.

The total cost is exactly
```
(9*A+3) + 8 + (9*L+15) + 20 + 3*(L+1) + 9
  + 3*(A+1) + 6 + 3*z + 30
= 12*(A+L) + 3*z + 97.
```
The total head displacement from the post-drain start is
```
-(3*A+1) - 2 -(3*L+5) + 4 + 3*z + 3
  + 3*(A+1) + 4 + 3*(L+1) - 4
= 3*z+5.
```

## Fixed finite bridge kernels

The following are head-relative `FConfig` traces. Mark lists are offsets
from the bridge's initial head; `inside` is the inclusive interval used
for the frame lift. The next counted sweep begins immediately to the
right of the interval, so the variable one-run is preserved by the bridge.

| Bridge | Steps | inside | Start | End (head offset, marks) |
|---|---:|---|---|---|
| B8 | 8 | [-3,1] | `(3,0,[-1])` | `(3,-2,[-3,-2,0])` |
| B20 | 20 | [-5,3] | `(3,0,[-3,-2,-1,2,3])` | `(3,4,[-5,-4,-3,-1,0,1])` |
| B9 | 9 | [-2,2] | `(3,0,[0,2])` | `(3,3,[-2,-1,0])` |
| B6 | 6 | [-1,3] | `(3,0,[2,3])` | `(3,4,[-1,0,1])` |
| B30 | 30 | [-4,5] | `(3,0,[-3,0])` | `(3,-4,[-2,-1,0,3,4,5])` |

For each row, `fRun tm2 n start = some end`; all intermediate heads
lie in `inside`. These are finite computations and can be discharged
with `decide`, then lifted over arbitrary exterior tape with
`BB6Coverage.Agent48Q4S0Macros.q4BridgeAt`.

## Where the variable sweep guards come from

Let `h0=-(3*A+3*L+8)` be the head after the two left scans and B8.
The bridge/sweep sequence places the right-sweep starts at:

- `h0+4`, with `L+1` consecutive `111` blocks;
- `h0+4+3*(L+1)+3`, with `A+1` consecutive `111` blocks;
- `h0+4+3*(L+1)+3+3*(A+1)+4`, with `z` consecutive `111` blocks.

The first two runs come from the two left-context unary regions; the final
run is the right unary counter. In particular, the final sweep starts at
absolute cell 9 when the original S0 head is 0, independently of A and L.
The bridge windows do not touch the sweep suffixes.
The remaining proof obligations are to derive these three `rightOnes`
predicates from the exact output of the preceding left scans/bridges and to
show that the three `sweptRight` outputs plus B30 give the target
`d0pow z ++ ell1` left-facing stream and `s0RightFacing 0` right-facing
stream. The final encoder identity uses
`binDec z (2^z-1) = d0pow z`.

## Final tape identity splits at cell 9

After B6 the head is at absolute cell 9, independent of A and L. The
left-facing stream beginning at cell 5 (four cells left of that head) is
exactly `ell1(A,L)`. This is the z-independent tail of the target and is
the remaining list identity to formalize from the two left scans, the L
sweep, B9, the A sweep, and B6.

B6's output frame sets cells 4,5,6 and clears cells 7,8. Thus the three
left-facing cells 8,7,6 are `0,0,1`, the final `d0` block. The z-sweep
starts at cell 9 and writes physical `100` blocks. Read backwards from the
final head `3*z+5`, its first `z-1` blocks give `d0pow (z-1)`; together
with cells 8,7,6 they give `d0pow z`. B30 moves the head from
`9+3*z` back four cells to `3*z+5`, without disturbing this left prefix.

At B30 entry, for z≥2, the ten cells at offsets -4 through +5 are exactly
`0,1,0,0,1,0,0,0,0,0`: offset -4 is cleared by block z-2, offset -3 is
the first cell of the final swept block, offsets -2 and -1 are cleared,
offset 0 is the extra trailing one of the original right counter, and the
five cells to its right are blank. The B30 output frame produces the
right-facing word `[0,1,1,1,0,0,1,1,1]`, namely `s0RightFacing 0`.

Consequently, the final tape proof can be split into two independent
identities: the z-sweep/B30 frame gives `d0pow z` and the right-facing
counter-zero word; the earlier prefix through B6 gives `ell1(A,L)` from
cell 5 leftward. This is substantially smaller than proving the entire
tape equality as one monolithic extensionality argument.

## Evidence and limits

I extracted all bridge endpoints and head paths from the original 12-entry
TM2 transition table at (A,L,z)=(4,2,3). The same component counts were
checked against several other small triples, including (3,2,2), (4,2,2),
(5,4,5), and (4,4,1). This is a trace decomposition, not a Lean proof or
an independently established universal theorem.

The displayed B30 kernel and the resulting `SetupSuffixGuards` composition
apply uniformly for `z ≥ 2). At `z=1`, the cell four positions left of the
B30 start is an unswept leading counter cell, so that boundary case needs a
separate finite B30 frame. The root instance has `z=2^63-1`, safely in the
uniform domain.

The decomposition is a concrete proof route: it replaces the single opaque
`12*(A+L)+3*z+97` setup run with two already-formalized left scans, three
already-formalized right sweeps, and five fixed finite bridges. The missing
work is now explicit tape algebra and the bridge/sweep composition, rather
than discovering the transition trace.
