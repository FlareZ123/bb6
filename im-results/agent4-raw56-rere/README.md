# Raw56 E1=1RE, E0=0RB — full candidate certificate cut

**Status: discovery complete; original-source Lean acceptance not yet established.** This is one five-hole child of Raw56, table `1RB---_1RC---_0RD---_1LD1LE_0RB1RE_------`. The intended exact-source theorem is `BB6.Agent4Raw56.RERB.all_quotient`, a universal weighted bound of 7014 for this compatible quotient cylinder. No Raw56 parent Cover, root-roster decrement or BB(6) upper bound follows yet.

## Candidate partition

A JavaScript BigInt tape enumerator used exact translated half-tape equality, cap 1000, lookback 32 and the canonical first-hole split. It found 1,181 split nodes, 21,726 translated-cycle leaves, 4,946 last-hole leaves (maximum query 573), and 492 open leaves. No aliases. A direct port of the repository FAR saturation and breadth-first DFA enumeration (up to five states, 42,182 automata/orientations) covered 487 open leaves.

All five remaining tables have finite two-stack run-language fixed points. The stack abstraction records the most recent `n` runs, lengths exact below `cap` and cyclic modulo `mod` thereafter, with a distinct infinite blank bottom. Every abstract configuration's outgoing push and every allowed inverse pop are closed in the finite relation. The invariant contains the blank configuration and no undefined instruction.

| Exact table | Symmetric stack parameters (n,cap,mod) | Joint states | Left/right stack states |
|---|---|---:|---:|
| `1RB1LC_1RC0LA_0RD0LF_1LD1LE_0RB1RE_---0LB` | 2,2,4 | 166 | 16/17 |
| `1RB---_1RC0LA_0RD0LF_1LD1LE_0RB1RE_1LB1LC` | 2,2,2 | 135 | 8/15 |
| `1RB0LF_1RC1LA_0RD0RE_1LD1LE_0RB1RE_---0LD` | 4,1,5 | 136 | 28/15 |
| `1RB1LF_1RC1LA_0RD---_1LD1LE_0RB1RE_0RA0LF` | 2,1,4 | 62 | 9/13 |
| `1RB1LF_1RC1LA_0RD---_1LD1LE_0RB1RE_0RE0LF` | 2,2,4 | 82 | 10/16 |

These are finite candidate certificates for unbounded nonhalting, not inferences from a simulation timeout. `spec.json` records the experimental counts and exact table-keyed parameters. The indices are from the JS enumeration and are not used as proof identities.

## Source closure

Run `python im-results/agent4-raw56-rere/prepare.py /tmp/raw56-rerb` from a repository checkout. This regenerates the original C++ first-hole tree and FAR5 witness bank, asserts every open table is covered by FAR or the five exact table-keyed RLE witnesses, emits literal two-stack certificates and bounded Lean subtrees, and prints file digests. It reuses the pinned original search sources and adapts Agent1's accepted Raw56 RCRD shard emitter. Compile the generated manifest in order, with original `TwoSidedAutomata`, `Raw40Nores`, `NGramCertificate` and their transitive source dependencies. The source-accepted Raw56 base artifact 15160313745 is a possible starting point; add the exact missing automata dependencies if absent. Acceptance requires `Raw56RERBAll.lean` and both exported theorem axiom profiles (standard axioms only).

The local shell and Python runtime were inaccessible (ClientError on simple commands), so neither local Lean nor the Python emitter was executed in this invocation. The JS experiments are complete; the generated-source acceptance remains a separate gate. Requested focused local compilation from Agent1 rather than launching a redundant workflow.

For the parent E1=1RE, this child is reached at the first undefined E0 query at time 10. It is one of eleven non-immediate-cycle E0 assignments. Even accepting this bound leaves ten sibling Covers to establish.
