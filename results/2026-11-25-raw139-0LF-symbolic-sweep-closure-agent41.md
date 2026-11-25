# Raw139 F/1 = 0LF: source-certified exhaustive weighted closure

**Theorem.** In the project’s weighted six-state semantics, every completion of the partial table `[7,24,11,24,14,21,3,16,12,11,24,20]` satisfies `WeightedBound 1603`. The bound includes the allowed initial-state weighting. This is an exhaustive certificate, not a finite-run claim.

**Proof status:** original-source Lean 4.36.0-rc2, standard axioms only, [successful pinned run 45604778890](https://github.com/FlareZ123/bb6/actions/runs/45604778890), source revision `4d2664e4caf8b2c0dbb41d0d842f8f4bae9b5488`, compiled artifact ID `15018045298`. The theorem is `BB6.Agent41F1ZeroLF.all_completions_weighted`.

The first-hole tree has 12 internal splits and 277 terminal leaves: 147 translated cycles, 72 last-hole queries, 45 FAR, and 13 all-time growth proofs. Max last-hole query: 1597. Each certificate is checked against its actual partial table.

## Reusable mathematical contribution

A symbolic zipper interpreter allows an arbitrary finite word at each opaque gap and rejects any read of a gap. Its theorem `run_sound` lifts a concrete symbolic finite-step check to all assignments of the gaps. Sweep induction then transfers repeated blocks at exact affine cost. This discharges twelve exceptional nonhalting cylinders.

The thirteenth requires a recursive carry grammar. Its six constructors have a structurally recursive successor and core cost. The outer sweep advances the repeat count by two and applies the counter successor; this family reaches its initial stage from blank and has positive exact costs for all successors. The carry theorem is an induction over the grammar, rather than over sampled runs. See the [full dossier and reproducible proof archive](../im-results/agent41-raw139-f1-zeroLF/README.md).

## Consequence and limitation

This closes one raw139 depth-five sibling at a small bound. Exact literal-table grafting into the global champion-score frontier is separate. Neither the remaining global roster nor the universal BB(6) upper bound is closed by this theorem.
