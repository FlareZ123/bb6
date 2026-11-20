# Root-specific q4Tail-to-S0 adapter instances

**Status:** source-level coordinate derivations, not Lean-compiled or CI-accepted. This note supplies authentic TM63 instances for Agent 42's generic adapter. It does not prove halting or determine BB(6).

## Generic adapter

Agent 42 committed `im-results/agent42-q4-s0-drain/Q4TailToS0Frame.lean`, theorem
`BB6Coverage.Agent42Q4TailToS0Frame.q4Tail_frame_eq_s0Config`.

For sweep start h and block count n>=2, it requires exactly:
1. T(h-1)=true;
2. T(h-2-i)=sideBit ell i for every i;
3. T(h+3*n+5+i)=false for every i.

It then proves
[
 frameAt (d0Sweep n T h) (h+3n) q4TailInside q4TailEnd
 = s0Config ell (n-1) (2^{n-1}-1) 0 (h+3n-5).
]
The generic d0-counter and nine-cell right-frame proofs are already isolated. The remaining work is to supply the three source conditions for the authentic root.

## Odd-q secondCyclePrefix34 branch

Use the definitions in `TM63RootQ4Tail.lean` and `PositiveZFirstCycleToSecondPrefix.lean`:
[
 a=2^z-1,quad n=2^a,quad m=3cdot2^z+3z+7,
]
[
 h_1=m+5,quad h=h_2=m+7,quad g=h+3n,quad H=g-5=m+2+3n.
]
Let
[
 tail0=replicate(4,true) ++ binDec(w,q) ++ lh,
]
the tail in `firstCycleS0DrainOutput z tail0`. Define
[
 tail_{34}=[1,0,0,1,1,1] ++ tail0.drop(6),
]
[
 ell_{34}=replicate(m+2,true) ++ [0,1,0,0] ++ tail_{34}.
]

For T2=afterFirstCycleTwoZero T1 h1, the three adapter obligations at sweep start h=m+7 are:

- **Left guard:** T2(h-1)=T2(m+6)=1 by the two-zero setup.
- **Residual ray:** for residual index j, the target cell is h-2-j=m+5-j.
  - j=0 is m+5, written 1 by setup.
  - j=1,...,m+1 covers m+4 down to 4. The existing proof's `linearRightOnes V 5 m` supplies cells 5 through m+4; the second-cycle frame marks cell 4.
  - j=m+2,...,m+5 gives cells 3,2,1,0, exactly 0100 from `secondCyclePrefix34End`.
  - j=m+6,...,m+11 gives cells -1,...,-6, exactly 100111 from the same frame.
  - j=m+12+k gives cell -7-k. These cells are outside both local frames and the left sweep, so they are the original S tape. At head m, the original left-facing index is m+7+k. Removing the d1pow(a) prefix of length 3a and the 3z+11-cell residual prefix leaves tail0 index 6+k:
[
 (m+7+k)-3a-(3z+11)=6+k.
]
  Thus the exact residual tail is tail0.drop(6), not an assumed blank suffix.
- **Blank right ray:** the adapter asks for T2(g+5+i)=0. This ray is outside the earlier frames, sweep, and setup. The original S0 right suffix is s0RightFacing(n-1), of length 6+3n; at g+5 its index is 3n+11, already beyond that length.

The resulting endpoint is s0Config ell34 (n-1) (2^(n-1)-1) 0 H. Since tail34 begins 100, Agent 44's corrected `p2S0DrainQ4Postlude` and `p2PostludeFrame_typeAWindow` can follow.

A useful simplification is
[
 tail0.drop(6)=(binDec(w,q) ++ lh).drop(2),
]
because tail0 begins with four ones.

## A=1 even-q branch: Type-C produces the same S0 shape

Agent 49 identified the parity-correct continuation when the outer P1 width is A=1. Then
[
 w=L+2,qquad q=2^{L+2}-2,qquad
 binDec(w,q)=d1 ++ d0pow(L+1).
]
The post-Q checkpoint V at head c has left-facing word
[
 oldLeft=[0,1,1] ++ d1 ++ binDec(w,q) ++ lh
       =[0,1,1] ++ d1 ++ d1 ++ d0pow(L+1) ++ lh.
]
This is exactly the Type-C input profile with tailL=d0pow(L)++lh.

The 46-step `typeC_to_state4` endpoint is a frame centered at c-7, with inside offsets 0 through 10 and marked offsets [10,8,5,2]. In absolute coordinates it marks c+3,c+1,c-2,c-5; every other cell in [c-7,c+3] is blank. The subsequent m-cell E-scan, two-zero setup, n-block d0Sweep, and q4Tail use
[
 h_1=c+4+m,quad h=h_2=h_1+2,quad
 g=h+3n,quad H=g-5.
]
The S0 residual begins at h-2=h1. Define
[
 tail_C=[1,0,0,1,0,0] ++ oldLeft.drop(8),
]
[
 ell_C=replicate(m+2,true) ++ [0,1,0,0] ++ tail_C.
]
At A=1, oldLeft.drop(8)=[1]++d0pow(L+1)++lh, so
[
 tail_C=[1,0,0,1,0,0,1] ++ d0pow(L+1) ++ lh.
]
In particular tail_C begins 100, again meeting Agent 44's postlude guard.

The residual proof is direct:
- j=0,...,m+1 gives h1 down through c+3: the setup cell h1, the m E-scan ones at c+4,...,c+m+3, and the Type-C frame's marked cell c+3;
- j=m+2,...,m+5 gives c+2,c+1,c,c-1 = 0100;
- j=m+6,...,m+11 gives c-2,...,c-7 = 100100 from the Type-C frame;
- j=m+12+k gives c-8-k, outside the Type-C frame, hence oldLeft index 8+k. This is exactly oldLeft.drop(8).

The left guard T2(h-1)=1 is the second setup cell. The far-right blank ray is beyond the same finite right suffix: the Type-C bridge preserves cells at and beyond c+4, the scan/setup/sweep end before g+5, and the source right stream is blank there. The full infinite-ray proof should reuse the original S0 right-suffix length rather than only the five local hzeros guards.

Applying Agent 42's adapter therefore gives
[
 s0Config ell_C (n-1) (2^{n-1}-1) 0 H.
]
This makes the A=1 Type-C route compatible with the same S0 drain/postlude interface. It exposes the remaining left word explicitly as tail_C; the terminal SectionBits continuation of d0pow(L+1)++lh is still open.

## Composition and limits

The odd-q branch and A=1 Type-C branch now have explicit candidate residuals for the same generic q4Tail-to-S0 adapter. After the adapter, Agent 44's S0 drain/postlude can apply because both residual tails begin 100; Agent 48's next-cycle prefix is the intended continuation. This links Agent 38's authentic blank-root-to-second-q4Tail run to the generic S0 adapter and the outer-width recurrence.

The A=1 tail formula does not finish the terminal SectionBits proof. The A=2 terminal case also remains to be closed. No halt, exact champion score, or universal six-state upper bound follows from these handoffs.

## Verification boundary

The supplied split files concatenate to an outer ZIP containing `lean-4.36.0-rc2-linux.tar.zst`. Extracting the ZIP alone does not install Lean; the additional step is:
`tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean`.
This is recorded in `AGENTS.md`. In this invocation, the local shell and Python tools returned ClientError before executing even trivial commands, so no local preflight was possible. The archive is not incomplete; the blocker is the tool boundary. Do not dispatch CI as a substitute for local preflight. All source-specific adapter instances above remain uncompiled.
