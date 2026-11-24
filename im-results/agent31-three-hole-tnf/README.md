# Complete three-hole weighted TNF subtree

Authentic first-eight-hole ancestor of Agent50's two-hole pilot: `1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_---0LA`. F0 is queried after 21 ordinary steps; all six live states have appeared. The three holes are A1, E0 and F0. The explicit certificate covers every ordinary child and halt sibling, hence 25³ = 15,625 compatible table completions.

Kernel-certified exact weighted threshold: **92**, attained by F0=1RA, A1=0LF, E0=halt after 91 ordinary moves plus final halt. No unchecked search cutoff is used as a verdict.

| Witness | Nodes |
|---|---:|
| Full expansions | 15 |
| Last-hole closures | 148 |
| Side-cycle nonhalt | 179 |
| Explicit FAR nonhalt | 19 |

Two independent finite enumerators agree on 1,123 halting and 14,502 nonhalting completions. The counts are auxiliary computational statistics, not the statement of the Lean theorem. The 19 residual growing-tape leaves were solved using Agent7's finite-automata reduction saturation, DFA sizes 1–9 and both orientations. Each DFA, NFA mask and zero mask is explicit; the checker verifies the invariant rules without relying on search heuristics.

## Files and verification

- `ThreeHoleAudit.lean`: reusable structural audit checker for arbitrary cut-six TNF parents. Converts explicit data to the existing `WeightedTNFCertificate`; checks all possible incoming blank delays.
- `ThreeHoleData.lean`: explicit full 361-node tree, authenticated parent path, exact upper and lower threshold.
- Manual `agent13-coverage.yml` target `weighted-tnf-three-hole` compiles the exact source closure and rejects placeholder/native-decision axioms. [Run 45409018102](https://github.com/FlareZ123/bb6/actions/runs/45409018102) succeeded: the exact source-closure check step completed successfully on Lean 4.36.0-rc2, including the axiom guard. Local Lean is installed, but GitHub DNS is blocked, so the original dependency closure is checked in CI.

This strictly enlarges the prior 625-completion pilot and is one local component of a future global TNF upper bound. It is not an exact BB(6) determination.
