# Raw34: exact certified nonhalting union of 97,539,062,500 physical machines

**Scope and status.** This is a substantive local family-classification advance toward BB(6), comprising several original-source kernel-accepted mathematical proofs plus a reproducible exact finite-set union calculation. It is **not** a complete Raw34 weighted Cover and **not** a universal upper bound for the six-state Busy Beaver function.

## Main result

For the six-state, two-symbol, initially blank-tape partial machine

```
Raw34 = 1RB---_1RC---_0RD---_1LC---_------_------
```

there are exactly `25⁸ = 152,587,890,625` physical total machine completions (24 ordinary actions plus one halt at each of eight unspecified state/symbol entries).

Combining the source-proven nonhalting cylinder theorems listed below, and counting their exact set-theoretic union over the eight physical instruction slots, **at least 97,539,062,500 distinct total completions are rigorously proved to never halt**. This is a certified nonhalting *subset*, not a claim that the remaining `55,048,828,125` completions halt or exceed any Busy Beaver bound.

| Source-accepted mathematical family | Original-source Lean run | New disjoint physical tables | Cumulative union |
|---|---|---:|---:|
| Eleven seven-hole D1 side-cycle cylinders | [46085109098](https://github.com/FlareZ123/bb6/actions/runs/46085109098) | 67,138,671,875 | 67,138,671,875 |
| Seventy-four six-hole depth-two side-cycles | [46085429345](https://github.com/FlareZ123/bb6/actions/runs/46085429345) | 18,066,406,250 | 85,205,078,125 |
| One six-hole exact unbounded unary-growth cylinder | [46085752374](https://github.com/FlareZ123/bb6/actions/runs/46085752374) | 244,140,625 | 85,449,218,750 |
| All 64 closed C–D control-pair cylinders | [46086179976](https://github.com/FlareZ123/bb6/actions/runs/46086179976) | 244,140,625 | 85,693,359,375 |
| 1,206 five-hole depth-three side-cycle cylinders | [46086787386](https://github.com/FlareZ123/bb6/actions/runs/46086787386) | 11,777,343,750 | 97,470,703,125 |
| All 1,728 closed B–C–D control-triple cylinders | [46086997664](https://github.com/FlareZ123/bb6/actions/runs/46086997664) | 39,062,500 | 97,509,765,625 |
| Two independent 4n+3 triple-sweep growth cylinders | [46087571719](https://github.com/FlareZ123/bb6/actions/runs/46087571719) | 19,531,250 | 97,529,296,875 |
| One 4n+4 alternating-block growth cylinder | [46087707935](https://github.com/FlareZ123/bb6/actions/runs/46087707935) | 9,765,625 | **97,539,062,500** |

The nonhalting theorems are genuine **universal statements over every unspecified transition**, not extrapolations from measured runtime. The finite side-cycle proofs employ sound orientation-sensitive half-line recurrence checks; the unary-growth proof establishes the exact increment recurrence `2n+3`; the two closed-control proofs induct on all-time closed state sets, independent of tape contents.

The **union arithmetic** is separate from the Lean proof objects. It is computed by the pure [count_accepted_union.mjs](../im-results/agent50-raw34-firsthole/count_accepted_union.mjs), which reads literal source witness tables, represents each proof as a wildcard conjunction of physical instructions, then computes the exact union by 25-way recursion, pruning when a proof covers all remaining unspecified entries. Its stage-by-stage numbers above, the unique four additional B–C–D triples, and the final complement were successfully reproduced in [CI run 46087926979](https://github.com/FlareZ123/bb6/actions/runs/46087244007), artifact [15240564330](https://github.com/FlareZ123/bb6/actions/runs/46087926979/artifacts/15240564330), SHA256 `0615ab9a7d9e702e37c68d7939d0ab2ec8648df3d605b3e72b394b00ae877338`. The script includes exact assertions for each cumulative cardinality, no probabilistic estimation, and keeps the literal halting instruction as one of the 25 physical options. Its input records are the same literal tables reproduced in the accepted Lean source modules.

## Underlying publishable proofs

- [Eleven plus seventy-four oriented side-cycles](2026-11-27-raw34-eightyfive-infinite-rays-agent50.md), 85 distinct children, using source-proved finite half-line recurrence soundness.
- [Exact unary-growth induction](2026-11-28-raw34-unary-growth-agent50.md), one apparently complex growing tape child, all-time `family n → family (n+1)`.
- [64 closed C–D pair theorem](2026-11-28-raw34-closed-component-agent50.md), discharging the second long depth-two machine by a graph invariant.
- [1,206 third-level oriented side-cycles](2026-11-28-raw34-depth3-1206-cylinders-agent50.md), all 23 source modules compiled and standard-axiom audited.
- [1,728 closed B–C–D triples](2026-11-28-raw34-bcd-closed-component-agent50.md), with four genuinely new long-running five-hole branches.
- [Three exact polynomial sweep-induction growth machines](2026-11-28-raw34-polynomial-growth-pumps-agent50.md), advancing the marked frontier in exactly 4n+3 (two branches) or 4n+4 (one branch) steps.

## Research significance and strict limitations

The two tape-independent control-component theorems are particularly useful: they prove nonhalting for entire large families whose individual finite executions may look irregular or unboundedly complicated. Their proof method generalizes to other finite-state subgraphs reachable from the blank start, and can be applied across the unresolved global canonical roster as a cheap candidate-closing mechanism before expensive symbolic tape induction.

However, about **36.08%** of Raw34 physical completions lie outside this certified nonhalting union. These are **unclassified** rather than halting. Some may halt quickly; others may run forever; others may require highly nontrivial arithmetic invariants. Neither a complete Raw34 Cover nor any one of the 40 source-accepted outstanding canonical global Cover obligations is discharged by this result. The preexisting exact champion remains a lower bound, not a proved universal BB(6) maximum.

The next decisive action is to combine a mathematically exhaustive Raw34 local partition with these sound certificates and prove the remaining halting-or-bounded cases. Then a **new source-checked global composition** must consume the resulting complete parent or exact quotient refinement. A table count by itself does not change the accepted global residual count.
