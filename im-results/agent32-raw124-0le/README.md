# Raw124 F1=0LE — complete candidate branch classification

Exact root table `1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LE`, 5 holes, 9,765,625 literal completions. Proposed original-semantics weighted bound 3006 (maximum query 2424, maximum cycle end 2940). **Full candidate closure, Lean audit not yet accepted.** No global roster reduction is claimed.

## Candidate partition and closure

Using Agent2's fast_partition.cpp at cap 3000/lookback 32: 51,778 cycle leaves (7,970,650 completions), 25,453 last-hole leaves and 3,617 splits (1,543,350 bounded completions), 5,961 open-discovery leaves (251,625 completions). Reuse of existing FAR bank yields 5,802 certificates. Symmetric run-length automata certify 101 additional leaves. Block-run automata certify all 58 remaining leaves. Every DFA candidate independently replayed with Agent16's witness fixed point; after context quotient, 13,906 total abstract configurations, maximum 899 per machine. Every hole is avoided in the finite abstract relation, not inferred from a finite blank trace.

The new stack abstraction reads a stack from far to near, ignores outer blank zeros, then groups symbols into fixed-width blocks (width 2–6), allowing an initial phase offset. It retains the last k runs of equal block symbols, each count truncated or periodic above a threshold. Partial blocks retain their exact bit contents and phase. The left and right deterministic push maps induce an inverse-pop relation; saturated reachable configurations must avoid every hole. The source proof emits existing IndexedBiDFA certificates and a closed structural weighted audit, so discovery and context quotient are not trusted by Lean.

## Reproduction

`python im-results/agent32-raw124-0le/replay_0le.py --out OUTPUT` regenerates the exact partition, asserts the SHA256 hashes in parameters.json, replays the fixed 193-code FAR bank, verifies all 159 indexed DFA candidates and emits original weighted checker source. Reuses Agent2 replay_fast_cut.py and Agent13 audit_shards.py without duplicating their logic. The final target is Raw124New0LEComplete.lean, theorem BB6.Agent2Raw124New0LE.bound_all. Proof status changes only upon full source acceptance.
