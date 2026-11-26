# q0 open-leaf finite automata

**Status: finite transition-closure certificates checked in JS; Lean original-source check pending.**

The earlier scan of 95 distinct open leaves is used as input; root28 is excluded because it already has a separate proof under audit. A forward primitive FAR saturation tracks a bounded run-length residue or n-gram DFA on one side and an NFA for the other. Reverse subset construction converts this into the two-stack relation already supported by `TwoSidedAutomata.lean`. For reflected searches, the stacks are swapped back before independently checking every original-direction transition. The blank seeds and every active row's push membership and all pop successors are checked. No bounded simulation is used as the certificate validity criterion.

| q0 root | Open leaves with checked finite relation | Total open leaves |
|---:|---:|---:|
| 26 | 13 | 13 |
| 33 | 1 | 1 |
| 34 | 4 | 4 |
| 39 | 16 | 16 |
| 44 | 5 | 5 |
| 46 | 1 | 1 |
| 48 | 2 | 2 |
| 49 | 19 | 21 |
| 51 | 31 | 31 |

For each successful leaf the generated relation gives a mathematical inductive nonhalting certificate for every compatible completion. The emitted Lean file invokes the existing `BB6.Agent4Automata.never` checker; exact transitive source compilation is still needed. The original Coq q0 forest also requires a source-semantic consumer, including all remaining sibling branches and exact root membership. Neither a new accepted global roster count nor an unconditional BB(6) bound is claimed.

Reproduce with `node q0-open-automata.cjs q0-open-root-scan-2026-11-26.json` in this directory. The JSON includes concrete automata and all active rows; the generator verifies closure on the original table. The current 80-root q0 Coq source run 45766737173 is independent.
