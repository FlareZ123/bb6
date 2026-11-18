# Marker-1 S0 first-q4-checkpoint normal form: expanded simulation evidence

**Status:** reproducible computational evidence and a candidate cost decomposition; no Lean proof of this checkpoint macro.

The new self-contained simulator
`marker1_q4_checkpoint_sweep.js` transcribes the TM2 transition table and
initial tape convention from
`im-results/agent48-counted-inc0/marker1_terminal_q4_checkpoint.py`.
The experiment detects the first state-4, head-1 checkpoint of

[
S_0(ell,A,z,0,h),qquad
ell=	ext{markerWord}(1)++d0++d1pow(L)++lh.
]

At that checkpoint, all tested cases had the following left-facing word:

[
[0,1,1]++operatorname{binDec}(A+L+2,M-1)++LH,
qquad
M=2^A(2^{L+2}-1).
]

The right-facing suffix from the checkpoint head is exactly

[
0^3,1^{3z+5},0^2,1^{3cdot2^z},0^4,
]

with no further nonblank cells. The number of state-4/read-0 events up to
the checkpoint is

[
E_{mathrm{prefix}}(z)=3cdot2^z+3z+5,
]

equal to the total number of ones in those two right-hand runs.

## Observed data

For (A=4,L=2):

| (z) | first checkpoint step | q4 events | right suffix |
|---:|---:|---:|---|
| 0 | 179 | 8 | (0^3 1^5 0^2 1^3 0^4) |
| 1 | 287 | 14 | (0^3 1^8 0^2 1^6 0^4) |
| 2 | 515 | 23 | (0^3 1^{11} 0^2 1^{12} 0^4) |
| 3 | 1,043 | 38 | (0^3 1^{14} 0^2 1^{24} 0^4) |
| 4 | 2,639 | 65 | (0^3 1^{17} 0^2 1^{48} 0^4) |
| 5 | 8,015 | 116 | (0^3 1^{20} 0^2 1^{96} 0^4) |
| 6 | 27,911 | 215 | (0^3 1^{23} 0^2 1^{192} 0^4) |
| 7 | 104,447 | 410 | (0^3 1^{26} 0^2 1^{384} 0^4) |
| 8 | 404,903 | 797 | (0^3 1^{29} 0^2 1^{768} 0^4) |
| 9 | 1,595,447 | 1,568 | (0^3 1^{32} 0^2 1^{1536} 0^4) |

The left-word equality, right suffix, and absence of further ones also
passed for (A=3,L=2,z=0,ldots,5) and (A=5,L=4,z=0,ldots,5).

## Exact intermediate S0 configurations and cost decomposition

Let (D(n)=\operatorname{drainCost}(n,0)), using the existing recursive
function from `CountedReset.lean`. The experiment identifies two exact
intermediate S0 configuration families, not only the final checkpoint.

Define the initial residual context

[
\ell_0=\operatorname{markerWord}(1)++d0++d1pow(L)++LH
]

and the second-drain residual context

[
\begin{aligned}
\ell_1(A,L)={}&11++(010)^{A+1}++011++110\\
&++(010)^L++011++101++11.
\end{aligned}
]

For every tested case, the following four-stage decomposition matches
the actual TM2 run exactly:

1. **Initial counted drain.**
   [
   S_0(\ell_0,A,z,0,0)
   \longrightarrow
   S_0(\ell_0,A,0,z,0)
   ]
   in (D(z)) steps. This is the existing
   `s0Config_counted_drain_general` interface.

2. **Setup macro (not yet proved).**
   [
   S_0(\ell_0,A,0,z,0)
   \longrightarrow
   S_0(\ell_1(A,L),z,2^z-1,0,3z+5)
   ]
   in exactly (12(A+L)+3z+97) steps.

3. **All-ones counted drain.**
   [
   S_0(\ell_1,z,2^z-1,0,3z+5)
   \longrightarrow
   S_0(\ell_1,z,0,2^z-1,3z+5)
   ]
   in (D(2^z-1)) steps. This is the existing
   `s0Config_counted_drain_closed` theorem at width (z), since
   (2^z-1) is the all-ones value of that width.

4. **Tail via existing `q4S0Postlude_at`.**
   Specialize the generic theorem in
   `im-results/agent48-counted-inc0/Q4S0FirstCycleMacros.lean` with
   `k=3*z+2` and start head `h=3*z+5`. The left-one hypothesis follows
   from `d1pow z ++ [1,1]`; the right guard is the first zero of
   `s0RightFacing (2^z-1)`. After the scan, the final-four guard is
   `0,1,0,0`: these are the first four bits of `ell1` after its initial
   `11`, and `s0LeftSweep_shift` leaves the new-head-left cells
   unchanged. The theorem gives exactly `3*(3*z+2)+4=9*z+10) steps
   and a `q4FrameAt` endpoint.

The two S0 drain stages are existing theorem interfaces. The **setup
macro** (stage 2) is the main remaining transition-proof obligation;
stage 4 only needs its hypotheses packaged and its generic `q4FrameAt`
endpoint identified pointwise with the explicit checkpoint tape. Summing
the four costs gives

## Postlude endpoint simplification

Agent 24 independently simplified the final frame. The residual context
`ell1` is equivalently

```
l2 = 110 ++ (100)^(A+1) ++ 111 ++ (100)^(L+1) ++ 1110111.
```

The pure list identity needed for the final left-facing word is

```
binDec(A+L+2, M-1) ++ LH
  = 00 ++ (100)^(A-1) ++ 111 ++ (100)^(L+1) ++ 1110111.
```

At the second-drain output head `h2=3*z+5`, the postlude scan uses
`k=3*z+2) and the final four-step frame ends at head 1. The total
head displacement is `3*z+4`. The long right unary block begins at
`h2+7=3*z+12), exactly where the final `1^(3*2^z)` run begins;
the postlude preserves it and constructs only the prefix
`0^3 1^(3*z+5) 0^2`. This gives a direct route from the generic
`q4S0Postlude_at` endpoint to the explicit checkpoint tape.

The second-drain output has right suffix
`s0RightFacing (2^z-1)`; the final tail turns it into
(0^3 1^{3z+5}0^2 1^{3\cdot2^z}0^4). The q4 event count at the final
checkpoint is (3\cdot2^z+3z+5), equal to the total number of ones in
that suffix.

The intermediate configurations and all four state/head/tape frames
were checked for (A=3,4,5,6), (L=2,4), (z=0,1,2,3). The final
checkpoint shape and cost formula were also checked through (z=9)
for (A=4,L=2). The reproducible script now checks all four stages:

```sh
node marker1_q4_checkpoint_sweep.js 4 2 9 3000000
```

This remains computational evidence, not a source proof. The separate
first q4 cycle *after* this checkpoint has the still deeper counted-drain
parameterization in `PositiveZFirstCycleDrainBridge.md`: with
(K=2^z-1), its observed cost matches an all-ones drain of width (K),
actual value (2^K-1), plus a further linear overhead. Its event-count
formula is also still unproved.


Agent 24 independently reproduced the four boundary tapes and
final checkpoint with a separate raw-step simulator,
`im-results/agent24-champion-time/verify_marker1_s0_two_drain_checkpoint.cjs`:
22 cases ((A,L)=(4,2), z=0..9; (3,2), z=0..5; (5,4), z=0..5),
2,170,886 primitive transitions, zero failures. Their residual context
`l2 = 110 ++ (100)^(A+1) ++ 111 ++ (100)^(L+1) ++ 1110111`
is exactly the same list as `ell1` above. This is independent
computational corroboration, not a universal proof.

## Setup macro trace clue

For the representative run (A=4,L=2,z=3), the raw setup trace
(after the first counted-drain output) begins with two existing
`state3_left_ones_scan` patterns:
- (k=3A+1=13), 39 steps from head 0, scanning `d1pow A` plus the
  first one of `markerWord 1`;
- an 8-step bridge;
- (k=3L+5=11), 33 steps scanning `d1pow L` plus its five-cell
  marker boundary.

These scans account for (9(A+L)+18) of the setup cost
(12(A+L)+3z+97). The remaining trace consists of short three- and
six-step patterns. This is a trace-derived decomposition for one
representative case, not a proof of the general setup macro. It is
shared with Agents 48 and 24 for possible composition with their
`state3_left_ones_scan` theorem.
