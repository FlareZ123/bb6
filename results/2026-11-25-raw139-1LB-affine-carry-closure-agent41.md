# Raw139 F/1 = 1LB: source-certified exhaustive weighted closure

**Theorem.** Every compatible completion of the literal partial table `[7,24,11,24,14,21,3,16,12,11,24,6]` satisfies `WeightedBound 172` in the project's weighted six-state semantics. The theorem is `BB6.Agent14F1OneLB.all_completions_weighted`.

**Proof status.** Original-source Lean 4.36.0-rc2 CI passed in [run 45628450059](https://github.com/FlareZ123/bb6/actions/runs/45628450059), at source revision `426ad87b1dd17a0e97026930fda15b924662c869`. The source-audit artifact is [15029118231](https://github.com/FlareZ123/bb6/actions/runs/45628450059), named `raw139-f1-oneLB-certified`. The deterministic reproducer checks the 1RF source archive and 1LB delta archive, reconstructs the proof modules, compiles the full original-source dependency closure, and audits the checked wrapper and final theorem against the standard axiom allowlist `propext`, `Classical.choice`, and `Quot.sound`.

The 9-split proof tree has 208 terminal leaves: 60 translated cycles, 49 last-hole queries, 54 FAR certificates, 43 affine sweep recurrences, and two structural carries. H36's translated cycle starts at step 738 with period 196. H11 is a binary 5-bit digit carry. H33 handles arbitrary unary-parametric digit lengths: the low form is `00 1^(n+4)`, the high form is `0000 1^(n+3)`; the carry transfers low-to-high, then high-to-low at length `n+1`, with the nil case returning to low 0. Both carry proofs induct over the tape suffix with arbitrary exterior, rather than relying on bounded simulation.

## Consequence and limitation

This closes the exact raw139 depth-five F/1=1LB cylinder at weighted bound 172. It is source-accepted, but its parent-to-frontier consumer has not yet been compiled. It therefore does not reduce the current 106-leaf residual count or establish a global BB(6) upper bound. The full intermediate dossier and reproduction command are in [`im-results/agent14-raw139-f1-oneLB/`](../im-results/agent14-raw139-f1-oneLB/README.md).
