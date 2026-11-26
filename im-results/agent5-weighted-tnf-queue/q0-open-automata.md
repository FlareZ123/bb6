# q0 open-leaf finite automata

**Status: all 94 targeted open leaves have finite primitive transition-closure certificates, independently regenerated and kernel-checked in Lean 4.36.0-rc2. Complete normalized parent proofs are being assembled; direct Rocq integration remains pending.**

The earlier scan has 95 distinct open leaves. Root28's one leaf already has a separate symbolic proof under audit and is excluded here. A forward primitive FAR saturation tracks a bounded run-length residue or n-gram DFA on one side and an NFA for the other. Reverse subset construction converts this into the two-stack relation already supported by `TwoSidedAutomata.lean`. For reflected searches, the stacks are swapped back before independently checking every original-direction transition. The blank seeds and every active row's push membership and all pop successors are checked. No bounded simulation is used as the certificate validity criterion.

| q0 root | Open leaves with checked finite relation | Total open leaves |
|---:|---:|---:|
| 26 | 13 | 13 |
| 33 | 1 | 1 |
| 34 | 4 | 4 |
| 39 | 16 | 16 |
| 44 | 5 | 5 |
| 46 | 1 | 1 |
| 48 | 2 | 2 |
| 49 | 21 | 21 |
| 51 | 31 | 31 |

The two root49 leaves not solved by primitive saturation are R49L14 and R49L18. They are solved by width-two forward block saturation, then a parity-pair lift of the block automata to primitive binary stack DFAs. At each push the lifted state records the full pairing, the complete prefix of the odd pairing, and the pending nearest bit. Adding a bit swaps the two alignments and consumes a block in the old odd alignment. A fresh primitive MITM reachable-closure check, with the original table and both full binary DFAs, certifies 222 and 174 rows respectively (112×34 and 28×17 stack states). The literal lifted DFAs are embedded in the reproduction script; thus the final certificates need no trusted block-macro semantics or tape-reflection theorem.

For each successful leaf the generated relation gives a mathematical inductive nonhalting certificate for every compatible completion. The emitted Lean file invokes the existing `BB6.Agent4Automata.never` checker; an independently regenerated set of exact-table certificates was accepted locally using the existing source-linked olean dependencies (artifacts 14996790073 and 15001870656), plus the exact TwoSidedAutomata source (blob c04bf81e19d55b3d028c714e628246a4b917f03c). The independently generated certificates need not be byte-identical to the checked-in JavaScript output. The original Rocq q0 forest also requires a source-semantic consumer, including all remaining sibling branches and exact root membership. Neither a new accepted global roster count nor an unconditional BB(6) bound is claimed.

Reproduce with `node q0-open-automata.cjs q0-open-root-scan-2026-11-26.json` in this directory. The JSON includes concrete automata and all active rows; the generator verifies closure on the original table. The independent 80-root q0 Rocq run 45766737173 reached its workflow timeout. The explicit finite-stack checker in Agent5SourceAutomata.v and q0-direct-auto.cjs avoids expensive MITM search in Rocq; CI acceptance remains pending.
