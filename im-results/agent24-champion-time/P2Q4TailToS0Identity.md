# Root-specific q4Tail-to-S0 adapter obligations

**Status:** source-level coordinate derivation, not Lean-compiled or CI-accepted. This note supplies the authentic root instance for Agent 42's newly committed generic adapter, rather than duplicating that adapter's counter/right-frame proof.

## Existing generic adapter

Agent 42 committed `im-results/agent42-q4-s0-drain/Q4TailToS0Frame.lean`, theorem
`BB6Coverage.Agent42Q4TailToS0Frame.q4Tail_frame_eq_s0Config`.

For a source tape T, sweep start h, and block count n, it requires exactly:

1. hleft: T(h-1)=true;
2. hres: for every i, T(h-2-i)=sideBit ell i;
3. hright: for every i, T(h+3*n+5+i)=false.

It then proves
[
 frameAt (d0Sweep n T h) (h+3n) q4TailInside q4TailEnd
 = s0Config ell (n-1) (2^{n-1}-1) 0 (h+3n-5).
]

The generic counter proof and the nine-cell right suffix are therefore already isolated. The missing task is to establish these three source conditions for the authentic TM63 second-cycle input.

## Root parameters and exact residual

Use the definitions in `TM63RootQ4Tail.lean` and `PositiveZFirstCycleToSecondPrefix.lean`:

[
 a=2^z-1,quad n=2^a,quad m=3cdot2^z+3z+7,
]
[
 h_1=m+5,quad h=h_2=m+7,quad g=h+3n,quad H=g-5=m+2+3n.
]

Let
[
 tail0 = replicate(4,true) ++ binDec(w,q) ++ lh.
]
This is the tail passed to `firstCycleS0DrainOutput z tail0`. Define
[
 tail1=[1,0,0,1,1,1] ++ tail0.drop(6),
]
[
 ell=replicate(m+2,true) ++ [0,1,0,0] ++ tail1.
]

Equivalently, because tail0 starts with four ones,
[
 tail1=[1,0,0,1,1,1] ++ (binDec(w,q) ++ lh).drop(2).
]
In particular tail1 begins with 100, exactly the guard required by Agent 44's corrected `p2S0DrainQ4Postlude`.

The intended root-specific application is
[
 q4Tail_frame_eq_s0Config n ell T2 h,
]
where T2 is the tape after `afterFirstCycleTwoZero T1 h1`, and h=m+7. Its output head is H.

## The three obligations

### 1. Left guard

[
 T2(h-1)=T2(m+6)=1.
]
This is immediate from `afterFirstCycleTwoZero`, which writes h1=m+5 and h1+1=m+6 to one.

### 2. Entire residual left ray

For every j>=0, the target cell is
[
 h-2-j=m+5-j.
]
The exact list ell is obtained by the following partition:

| Residual index j | Absolute cell | Source |
|---|---:|---|
| 0 | m+5 | two-zero setup writes 1 |
| 1,...,m+1 | m+4,...,4 | the existing `linearRightOnes V 5 m` fact supplies cells 5 through m+4; the second-cycle frame marks cell 4 |
| m+2,...,m+5 | 3,2,1,0 | `secondCyclePrefix34End` writes 0100 |
| m+6,...,m+11 | -1,-2,-3,-4,-5,-6 | the same frame writes 100111 |
| m+12+k, k>=0 | -7-k | unchanged original S0 tape; this is tail0 index 6+k |

For the last row, the original S0 head is m. At x=-7-k its left-facing index is m+7+k. The original left stream is
[
 d1pow(a) ++ firstCycleResidualLeft(z,tail0),
]
where the first two lengths are 3a and 3z+11 (the latter includes the leading 1-run and 0100 boundary). Thus the index into tail0 is
[
 (m+7+k)-3a-(3z+11)=6+k,
]
using a=2^z-1 and m=3*2^z+3z+7. Therefore the exact remaining source list is tail0.drop(6). No assumption that the distant left tape is blank, and no separate inequality such as 2^z>w, is needed.

The support check is straightforward: the first-cycle postlude frame is supported on absolute cells 0 through 3; the second-cycle 34-frame is supported on -6 through 4; the left sweep changes cells only from 4 through m+1; the two-zero setup changes m+5,m+6; and the later d0 sweep begins at m+7. Consequently all cells <=-7 retain the original S tape.

The one sublemma worth factoring out of the existing proof is the right-one run on V: for 5<=x<=m+4, V(x)=true. The current proof already establishes this as `hfirst : linearRightOnes V 5 m`, using `s0LeftSweep_shift` on 5..m+1 and the first three one-cells of `s0RightFacing (2^a-1)` on m+2..m+4. The second-cycle frame separately gives T1(4)=true.

### 3. Blank right ray

For every i>=0, the required cell is
[
 h+3n+5+i=g+5+i=m+12+3n+i.
]
It is beyond every operation before the q4Tail frame:
- first-cycle postlude frame: absolute support 0..3;
- second-cycle 34-frame: absolute support -6..4;
- left sweep: at most m+1;
- two-zero setup: m+5,m+6;
- d0 sweep: m+7 through g-1.

So T2 at this coordinate is the original S tape. Its right-facing suffix is `s0RightFacing (n-1)`, of length 6+3n. The source-side index is
[
 (g+5+i)-m-1=3n+11+i,
]
strictly beyond that length. Hence the cell is blank for every i.

## Composition unlocked

These three facts give the exact input to Agent 42's generic adapter. The resulting configuration is
[
 s0Config ell (n-1) (2^{n-1}-1) 0 H.
]
Because ell is exactly `p2ResidualLeft m tail1` and tail1 begins 100, Agent 44's `p2S0DrainQ4Postlude` and `p2PostludeFrame_typeAWindow` can be applied directly. Agent 48's `p2S0_to_next_q4Tail` then supplies the next q4Tail cycle, with
[
 m'=H=m+2+3n,qquad n'=2^{n-1}.
]

This joins the existing authentic blank-root-to-second-q4Tail theorem (Agent 38) to the generic S0 adapter (Agent 42), the corrected postlude (Agent 44), and the next-cycle prefix (Agent 48). It makes the two-d0-block outer-width descent usable without inventing a blank far-left tail.

The terminal positive-z cases A=1 and A=2 remain open. No halt, exact champion score, or universal six-state upper bound follows yet.

## Verification boundary

The derivation is source-level and not Lean-compiled. The local shell and Python execution tools returned ClientError in this invocation, and the repository's root-q4Tail dossier records that the supplied split Lean archive is incomplete. Do not dispatch CI as a substitute for exact local preflight. The next useful action is to formalize the three root obligations against Agent 42's adapter, factor the existing `hfirst` lemma if needed, and compile the exact dependency closure once a complete local Lean 4.36.0-rc2 toolchain is available.
