# Raw139 F/1 = 1RD: source-certified exhaustive weighted closure

**Theorem.** Every compatible completion of the literal partial table `[7,24,11,24,14,21,3,16,12,11,24,15]` satisfies `WeightedBound 489` in the project's weighted six-state semantics. The theorem is `BB6.Agent14F1OneRD.all_completions_weighted`.

**Proof status.** Original-source Lean 4.36.0-rc2 CI passed in [run 45628462126](https://github.com/FlareZ123/bb6/actions/runs/45628462126), at source revision `426ad87b1dd17a0e97026930fda15b924662c869`. The source-audit artifact is [15029402030](https://github.com/FlareZ123/bb6/actions/runs/45628462126), named `raw139-f1-oneRD-certified`. The deterministic reproducer reconstructs the 1RF base, 1LB emitter dependency, and 1RD delta, compiles the complete source closure, and audits the checked wrapper, final theorem, and all 53 growth/never theorems against `propext`, `Classical.choice`, and `Quot.sound`.

The 9-split proof tree has 208 terminal leaves: 94 translated cycles, 45 last-hole queries, 16 FAR certificates, and 53 affine growth proofs. The FAR witnesses have sizes 4, 5, and 6 (six, two, and eight respectively); discovery uses canonical breadth-first state naming for reachable DFAs. The central H22 recurrence is an eight-phase block pump beginning at step 2 in state C, with left word `011` and right word `(0011)^(8n)`; each return inserts eight copies of `0011`. The full intermediate dossier, deterministic replay, and reproduction command are in [`im-results/agent14-raw139-f1-oneRD/`](../im-results/agent14-raw139-f1-oneRD/README.md).

## Consequence and limitation

This closes the exact raw139 depth-five F/1=1RD cylinder at weighted bound 489. It is source-accepted, but its parent-to-frontier consumer has not yet been compiled. It therefore does not reduce the current 106-leaf residual count or establish a global BB(6) upper bound.
