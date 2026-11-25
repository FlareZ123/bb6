# Exact finite maximum for the raw110 six-hole cylinder

**Theorem (Lean 4.36.0-rc2, 25 November 2026).** Every ordinary six-state two-symbol completion of the partial table

`1RB---_1RC---_0RD---_1LD1RE_---0LC_------`

either never halts or halts within 6,766,859 steps, including the final halt. The bound also holds in the repository's weighted first-one reduction. There are exactly 25^6 = 244,140,625 completions in the standard normalized halt/ordinary-move convention. The maximum is attained by the completion

`1RB1RZ_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC1RD`.

The choice of write/direction on the halt transition does not change its counted score. This is a resolved entire cylinder in the canonical reduction, not a global BB(6) upper bound.

## Proof

The first missing query in the partial table is C1 after seven defined moves. A sound first-hole audit recursively covers the ordinary children, using translated cycles, finite automata invariants, and symbolic nonhalting certificates. Its weighted bound is 7014 on the closed subtrees. Exactly two retained one-hole partial tables remain, with F1 equal to 0LF or 1RD and all other rows fixed except A1.

For each, a proved exact paired-word sweep evaluates the execution in the primitive semantics. The run-length representation of the repeated right A-pair and left bit runs is proved equivalent to the original sweep evaluator, with exact primitive-step cost, including the alignment change at the edge of the right word. The 19203 sweeps terminate at A1 after 6,659,486 and 6,766,858 defined moves, respectively. Each partial table has 24 ordinary completions, which are total and never halt, and a halt completion with score one greater than its defined-move count. The original-source bridge proves the blank-delay list [0] for each halting completion. This proves the two weighted covers at the displayed scores, and hence a cover at the larger score for the entire parent. The explicit slow halt completion realizes it.

## Source and reproducibility

- [Parent closure theorem](../im-results/agent7-raw110/Raw110ParentLateCover.lean): `BB6.Agent7Raw110.raw110_cover (B : Nat) (hB : 6766859 ≤ B) : Cover (WeightedBound B) p110`.
- [Original source semantics bridge](../im-results/agent7-raw110/Raw110WordSource.lean), [concrete bounds](../im-results/agent7-raw110/Raw110LateCover.lean).
- [Paired sweep](../im-results/agent7-raw110/Raw110WordSweep.lean), [run-length acceleration](../im-results/agent7-raw110/Raw110RunSweep.lean), [trace generator](../im-results/agent7-raw110/gen_late_trace.py).
- [Exact parent partition and residual matches](../im-results/agent7-raw110/Raw110ParentResidualMatch.lean).
- [Complete source proof dossier](../im-results/agent7-raw110/README.md).
- [Successful end-to-end CI 45597857116](https://github.com/FlareZ123/bb6/actions/runs/45597857116), artifact `raw110-complete-parent`; all prior partition artifacts are recorded in the dossier. The complete run checked the concrete trace shards, original-source bridge, and parent composition. No `sorryAx` or `native_decide` is accepted.
