# Agent 5: block-FAR → original Coq primitive MITM

The finite right NFA of a block-FAR certificate can be reverse-determinized (start subset = blank-accepting nodes). Both resulting block DFAs can be lifted to bit DFAs by tracking every block alignment at once. A local full primitive push/pop closure check, with all inverse edges, closed all eight block-FAR q0 held tables. In source orientation:

| q0 offset | left DFA | right DFA | full primitive abstract configurations |
|---|---:|---:|---:|
| 0 | 10018 | 20470 | 1465332 |
| 300 | 2416 | 1939 | 14684 |
| 400a | 3833 | 1686 | 14447 |
| 400b | 125 | 26 | 461 |
| 600 | 273 | 38 | 1032 |
| 700 | 4284 | 2177 | 124496 |
| 2700 | 2966 | 1845 | 5443 |
| 2800 | 969 | 570 | 32733 |

Separately, q3500's symbolic recurrence admits a simple primitive BiDFA: four nearest runs, each length modulo 9, blank-only summary 0. The discovered-edge closure has 145 left and 131 right states and 1129 configurations.

Generator: `im-results/agent5-weighted-tnf-queue/block_phase_dfa.py`, using Agent13's existing generator with an added return value (no change to Lean emission). Original BusyCoq MITMDFA certificate batches completed successfully, run 45607275287 (600,400b,2700,300) and 45607737965 (3500,400a,2800,700,0); each success asserts at least one accepted certificate, not necessarily all. Their artifacts retain individual verdicts and exact source proofs.

The direct source-consumption workflow is now dispatched: `enumerate62-phase-consume`, using accepted `.vo` artifacts and recovered exact packed q0 checkpoints. It proves complement equivalences, retaining every unmatched active/held node, and evaluates exact consumed counts. Do not add isolated leaf masses to canonical77/global counts. This route is particularly useful where a Lean proof is accepted but source Coq coverage remains open. The full phase product is general; modular run summaries may be much smaller.

No universal BB(6) upper bound follows yet.