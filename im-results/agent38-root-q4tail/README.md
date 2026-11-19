# Authentic TM63 root to q4Tail and the corrected P2 S0 handoff

## Established source chain and scope

`TM63RootQ4Tail.lean` is an intermediate composition of two existing source drafts:

1. Agent 48's `tm63_blank_reaches_second_q4_frame`, from the authentic blank root to the first-cycle q4 endpoint;
2. Agent 24's `positiveZFirstCycle_then_secondCyclePrefix`, from that canonical q4 checkpoint through the first cycle and the second-cycle prefix to `q4Tail`.

The wrapper extracts the exact C2 suffix from the shared C1 endpoint using `run_append`, then transports it to the authentic root coordinate with `shift_run`. The only new arithmetic side condition is oddness of `firstQ4P1Value`, supplied by the existing BinDec capacity and root-`z` bounds.

**The root wrapper and its dependencies remain uncompiled source drafts.** This does not establish a halt, an exact champion score, or a global BB(6) upper bound.

## Correct P2 residual boundary

The earlier `P2ResidualBoundaryAudit.md` and the 73-step 0101 branch are superseded. They misread the semantics of `frameAt`.

The authoritative lemma `frameAt_tape` in `im-results/agent6-q4-prefix/CountedQ4Prefix.lean` states that, inside the frame, the tape is `decide (x-h ∈ c.marked)`. Thus **every unmarked cell inside the frame is written blank**; it does not retain its input bit.

For checkpoint head (h=1), put
[
m=3cdot2^z+3z+7,quad n=2^{2^z-1},quad
h_1=m+5,quad h_2=m+7,quad g=m+7+3n,
]
and (H=g-5=m+2+3n, a=n-1). The S0 counter `binDec a (2^a-1)=d0pow a` has length (3a), so the residual left context after that counter begins at
[
H-3a=m+5.
]

The two-zero setup writes cells (m+5,m+6) to one. The E-scan contributes the (m) ones at cells (5,ldots,m+4), and the 34-step frame marks cell (4) as one. These give the leading (1^{m+2}).

The 34-step frame has marked offsets ([-7,-6,-5,-2,1,3]) relative to (h=1). Because unmarked cells inside its window are blank, its next four cells at coordinates (3,2,1,0) are exactly
[
(0,1,0,0).
]
Its next three cells at (-1,-2,-3) are exactly
[
(1,0,0).
]
Therefore the authentic residual has the form
[
1^{m+2};0100;	ext{tail},qquad 	ext{tail begins }100.
]

This is the interface required by Agent 44's generic `S0DrainQ4Postlude.lean`. The next task is to prove the full q4Tail-to-`s0Config` tape identity, including the d0 counter and the right-facing `s0RightFacing 0` suffix. The residual prefix and the 100 tail guard are not by themselves a completed handoff.

## Conditional 0101 branch

`P2ActualBoundaryBridge.lean` is a valid finite 73-step bridge for its stated conditional input `0101 1^7 00`. It is **not** the authentic TM63 continuation and must not be composed with `rootSecondQ4TailFrame`.

Agent 48's `P2ActualBoundaryComposition.lean` is likewise a conditional theorem for that different S0 input family. Preserve it as an independent finite-trace result, but do not describe it as an actual root continuation.

## Toolchain / verification status

The uploaded Lean archive is incomplete: concatenating the two supplied parts produces 526,200,098 bytes, while the ZIP directory requires 608,393,640 bytes (82,193,542 bytes are missing). The partial archive decompresses only part of the toolchain and contains no `bin/lean`. Thus the exact Lean 4.36.0-rc2 local preflight could not be run in this invocation. The source remains uncompiled and no axiom audit is claimed.

## Next mathematical obligations

1. Prove the pointwise q4Tail-to-S0 identity for `rootSecondQ4TailFrame`: left-facing stream `d0pow (n-1) ++ p2ResidualLeft m tail`, right-facing stream `s0RightFacing 0`.
2. Use the tail beginning `100` to apply Agent 44's `p2S0Drain_q4Postlude` and `p2PostludeFrame_typeAWindow`.
3. Identify the resulting state-4 frame at head 1 with the next canonical checkpoint and compose the next P1/P22 iteration.
4. Compile the ordered import closure under Lean 4.36.0-rc2 and audit exported theorem axioms when a complete local toolchain is available.

All material here remains under `im-results/`. No result has been promoted to `results/`; BB(6) remains unresolved.
