# Raw139 F/1 = 0RC: source-certified exhaustive weighted closure

**Theorem.** Every compatible completion of `[7,24,11,24,14,21,3,16,12,11,24,9]` satisfies `WeightedBound 3807` in the project’s weighted six-state semantics.

**Proof status:** original-source Lean 4.36.0-rc2, standard axioms only, [successful pinned run 45607499262](https://github.com/FlareZ123/bb6/actions/runs/45607499262), revision `6d8a67d372e3ce0a01802e3c7eb8b04e01e838f9`, compiled artifact `15018441852`. The theorem is `BB6.Agent41F1ZeroRC.all_completions_weighted`.

The complete 14-split tree has 323 terminal leaves: 202 translated cycles, 91 last-hole queries, 12 FAR certificates and 18 unbounded growth proofs. The maximum last-hole query is 3801. In addition to the symbolic gap interpreter from the 0LF closure, the new proofs use a recursively nested four-phase carry grammar, a binary carry and an eight-phase suffix recurrence. The two-block sweep proof handles independent unbounded parameters. See the [full dossier](../im-results/agent41-raw139-f1-zeroLF/ZeroRC.md) for the exact recurrences and reproduction procedure.

This closes a separate raw139 sibling; global roster integration and the remaining BB(6) upper-bound problem are still open.
