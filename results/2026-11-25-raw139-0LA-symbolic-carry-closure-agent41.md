# Raw139 F/1 = 0LA: source-certified exhaustive weighted closure

**Theorem.** Every compatible completion of the literal partial table `[7,24,11,24,14,21,3,16,12,11,24,0]` satisfies `WeightedBound 553` in the project's weighted six-state semantics. The theorem is `BB6.Agent14F1OneLA.all_completions_weighted`.

**Proof status.** Original-source Lean 4.36.0-rc2 CI passed in [run 45628441572](https://github.com/FlareZ123/bb6/actions/runs/45628441572), at source revision `426ad87b1dd17a0e97026930fda15b924662c869`. The source-audit artifact is [15029897763](https://github.com/FlareZ123/bb6/actions/runs/45628441572), named `raw139-f1-zeroLA-certified`. The deterministic reproduction script verifies the 1RF source archive and 0LA delta archive, reconstructs all proof modules, compiles the full dependency closure, and audits the checked wrapper and final theorem against the standard axiom allowlist `propext`, `Classical.choice`, `Quot.sound`.

The 9-split proof tree has 208 terminal leaves: 41 translated cycles, 45 last-hole queries, 83 FAR certificates, 28 affine growth proofs, and 11 recursive carry proofs. The eleven carry proofs share an outward sweep (9-step setup and repeated 4-step transfers) and inward 3-step sweeps. At an odd leading unary length, the core acts on a structurally recursive binary or four-valued digit word, returns at state E over an arbitrary left exterior, and reconstructs the growing unary run. H13 inserts one leading one and advances an odd-length family directly; the other ten alternate parity. `LAOuter.lean` proves the common phase composition, while `gencarry.py` emits the exact flavor-specific structural inductions.

## Consequence and limitation

This closes the exact raw139 depth-five F/1=0LA cylinder at weighted bound 553. It is a source-accepted sibling certificate, but its parent-to-frontier consumer has not yet been compiled. It therefore does not reduce the current 106-leaf residual count or establish a global BB(6) upper bound. The full intermediate dossier and reproduction command are in [`im-results/agent14-raw139-f1-zeroLA/`](../im-results/agent14-raw139-f1-zeroLA/README.md).
