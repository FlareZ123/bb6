# Raw139 E0=1LA exceptional leaf 8938: exact buffered dynamics

**Intermediate, not a decision.** Exact table `[7,8,11,21,14,13,17,16,2,11,19,24]` (code 4*q+2*w+r, F1 unassigned). Agent48's E0=1LA census has this as its remaining candidate-unclassified leaf. Do not count this as a Cover.

The 5 phases are cr (C scanning right with known left 1), cl (C scanning left with known right 0), el (E scanning left with known right 01), er0 (E scanning right with known left 00), er1 (E scanning right with known left 1). Stacks L,R nearest first, with infinite zero suffixes, omit these fixed buffers. The authentic blank run enters cr(L=1,R=empty) after two steps.

| Phase | Pop L | Pop R | Next | Push L | Push R | Cost |
|---|---|---|---|---|---|---:|
| cr | | 0 | el | | | 2 |
| cr | | 11 | cl | | 10 | 4 |
| cr | | 10 | er0 | 1 | | 2 |
| cl | 1 | | er0 | | | 2 |
| cl | 00 | | el | 0 | | 5 |
| cl | 01 | | el | | 0 | 2 |
| el | 1 | | el | | 1 | 3 |
| el | 00 | | cr | 101 | | 5 |
| el | 01 | | cl | | 101 | 2 |
| er0 | | 1 | cr | 00 | | 1 |
| er0 | | 00 | er1 | 010 | | 4 |
| er1 | | 1 | cr | 1 | | 1 |
| er1 | | 0 | cl | | 1 | 2 |

The sole uncovered case er0 R=01R' reaches F1 in exactly three known ordinary moves, independently of L and R'. Every other configuration is covered after appending two zeros to each stack. Every arrival at cl has R beginning in 1, so cl->er0 cannot itself introduce bad; the other bad preimage is cr R=1001R'. This is a useful whole-sweep safety target.

Unpack with `python3 unpack.py`; the Lean module imports SparseZipper. Locally compiled with Lean 4.36.0-rc2 against a minimal exact-definition copy of Frontier/RootShift and the copied SparseZipper proof bodies, not a full original-source audit. Theorems rule_exact, bad_hit, seed_run, stable_never use propext and Quot.sound only; cover_padded uses propext only. stable_never is conditional on a Stable invariant (seed, padding, bad exclusion, closure under the 13 rules). No invariant has yet been supplied. The independent primitive replay of 100M steps is finite evidence only.

Prior broad fixed-block and prefix/run abstractions failed or hit caps; do not interpret this as a halt. Scanner-end monoid refinements also admit spurious bad paths. Work on the exact sweep transducers and a joint invariant rather than repeat primitive scans. No new workflow.
