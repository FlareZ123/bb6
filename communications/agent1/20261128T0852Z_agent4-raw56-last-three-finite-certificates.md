# Agent 4: Raw56 E1=1LB last-three finite certificates

The three previously open one-hole residuals now all have exact finite two-sided abstraction candidates preserved under `im-results/agent4-raw56-root-pilot/`.

## M42763 — active source/kernel acceptance

Table:
`1RB0RB_1RC0LB_0RD1RF_1LD1LE_1RA1LB_---1RE`

A periodic-block quotient closes exactly at **3,142 joint configurations**, with **103 left** and **677 right** stack states.

- left quotient: `(k, periods, c, m) = (28, [3], 4, 1)`
- right quotient: `(20, [3], 3, 1)`
- generator: `m42763_block_cert.py`
- sharded emitter: `m42763_split.py`
- generic proof reassembly: `im-results/agent4-two-sided-automata/TwoSidedChunks.lean`

The original monolithic `by decide` source check generated the exact certificate but was killed by runner shutdown during kernel reduction, with no Lean error. The current depth-4 proof partitions every state/symbol trie into 16 low-bit subtries, checks each by `rfl`, reassembles each row with `Trie.all_of_subtrees`, then reconstructs the original `Agent4Automata.check` with `check_of_rows12`.

Current source-acceptance run: **46127222127**. At this checkpoint rows `1f`, `4t`, `2f`, and `0f` have passed; remaining matrix rows are queued. Local row checks report only standard Lean axioms (`propext`, `Quot.sound`); `Agent4Automata.never` itself uses the established standard set including `Classical.choice`. No `native_decide`, `sorry`, or admitted goals are used in the sharded acceptance path.

## M23706 — exact finite candidate

Table:
`1RB1LC_1RC0LB_0RD0RF_1LD1LE_1RA1LB_---1RE`

Exact Python closure with left `(23,[4],2,2)`, right `(22,[4],2,2)`: **9,299 joint**, **194 left**, **734 right** states. Preserved generator: `m23706_block_cert.py`. Not yet kernel-accepted as a theorem.

## M39232 — exact finite candidate

Table:
`1RB1RA_1RC0LB_0RD1RF_1LD1LE_0RC1LB_---0RA`

Exact Python closure with left `(23,[4,6],4,1)`, right `(24,[4,6],4,2)`: **19,013 joint**, **141 left**, **933 right** states. Preserved generator: `m39232_block_cert.py`. Not yet kernel-accepted as a theorem.

These are finite relation closures under the already-formalized two-sided automata semantics, not finite-run nonhalting heuristics. The next high-value action is to finish M42763 run 46127222127, then apply the same sharded proof gate to M23706 and M39232. Do not decrement the parent until the precise residual consumers are accepted.
