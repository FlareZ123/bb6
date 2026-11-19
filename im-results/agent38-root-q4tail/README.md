# Authentic TM63 root to q4Tail and the corrected P2 continuation

## Established source chain and scope

`TM63RootQ4Tail.lean` is an intermediate composition of two existing source drafts:

1. Agent 48's `tm63_blank_reaches_second_q4_frame`, from the authentic blank root to the first-cycle q4 endpoint;
2. Agent 24's `positiveZFirstCycle_then_secondCyclePrefix`, from that canonical q4 checkpoint through the first cycle and the second-cycle prefix to `q4Tail`.

The wrapper extracts the exact C2 suffix from the shared C1 endpoint using `run_append`, then transports it to the authentic root coordinate with `shift_run`. The only new arithmetic side condition is oddness of `firstQ4P1Value`, supplied by the existing BinDec capacity and root-`z` bounds.

**The root wrapper and its dependencies remain uncompiled source drafts.** This does not establish a halt, an exact champion score, or a global BB(6) upper bound.

## Corrected P2 residual boundary

The proposed downstream interface in `im-results/agent44-p2-postlude/S0DrainQ4Postlude.lean` assumes a residual beginning `1^(m+2) ++ 0100 ++ tail`, with a `100` tail guard. That is incompatible with the current authentic second-cycle prefix.

For checkpoint head (h=1), put
[
m=3\cdot2^z+3z+7,\quad n=2^{2^z-1},\quad
h_1=m+5,\quad h_2=m+7,\quad g=m+7+3n,
\]
and (H=g-5=m+2+3n), (a=n-1). The S0 counter `binDec a (2^a-1)=d0pow a` has length (3a), so the residual context after it begins at
[
H-3a=m+5.
]

The two-zero setup and E-scan contribute (m+1) consecutive ones from cells (m+5) through (5); the 34-step endpoint marks cell (4=h+3) as one, giving (m+2) leading ones. The exact `secondCyclePrefix34End` frame has marked offsets ([-7,-6,-5,-2,1,3]). With the stated input window, the next four cells (3,2,1,0) are therefore (0,1,0,1): offsets (+2,0) remain zero, (+1) is marked one, and offset (-1) is an unmarked input one. The later two-zero setup, d0 sweep and q4Tail frame do not touch cell (0=h-1).

The actual residual starts
[
1^{m+2}\;0101\;1^7\;00\;\cdots,
]
not (1^{m+2}0100) with a (100) tail. In particular, the proposed S0/postlude target has the wrong bit at cell (0), and its tail guard is also false. Do not compose the current q4Tail theorem with that proposed target.

The full coordinate audit is in [P2ResidualBoundaryAudit.md](P2ResidualBoundaryAudit.md).

## Replacement finite continuation draft

`P2ActualBoundaryBridge.lean` records a finite 73-step bridge for the actual post-sweep window. Relative to the state-3 start head (h), its input is:
- (T(h)=0), (T(h-1)=1), (T(h-2)=0), (T(h-3)=1);
- (T(h-4),\ldots,T(h-10)=1);
- (T(h-11)=T(h-12)=T(h+1)=0).

The finite trace ends in state 4 at head (h-1), with (h-1,h,h+1) all one. The draft includes the exact finite trace and head-bound checks by `decide`, and an arbitrary-exterior lift through `bridgeAt`.

The same module contains a generic right-continuation draft: from state 4 at head (2), if cells (2\ldots H+4) are one, cells (H+5,H+6) are zero, and a `d1BlocksOn` run of length (2^a) follows, the source run converts those blocks to `d0Sweep` and reaches state 2 at (H+6+3\cdot2^a), with the exact accumulated tape written in the theorem statement. This is a conditional local macro, not yet a proof that the full S0 handoff satisfies all hypotheses.

**Neither the 73-step bridge nor the right-continuation theorem has been Lean-compiled or axiom-audited.** The local Python/container/shell tools in this invocation returned tool-level errors, so no local preflight was available. No CI was dispatched. Agent 44 was asked to preflight the exact bridge source and repair the first diagnostic if available.

## Next mathematical obligations

1. Preflight the exact `P2ActualBoundaryBridge.lean` dependency closure under Lean 4.36.0-rc2 and audit exported theorem axioms.
2. Prove that the authentic S0 drain output, with the corrected (1^{m+2}0101,1^7 00) residual, satisfies the 73-step bridge's exact input window after the left sweep.
3. Compose the bridge with the right one-run, two-zero transition and `d1BlocksOn` continuation; identify the resulting state-2 endpoint with a reusable S1/S0 section or derive its next exact macro.
4. Only then continue the authentic root toward the terminal section and exact score.

All material here remains under `im-results/`. No result has been promoted to `results/`; BB(6) remains unresolved.
