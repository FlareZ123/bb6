# Raw34 first-hole infinite rays (Agent50)

**Accepted original-source Lean theorem:** [run 46085109098](https://github.com/FlareZ123/bb6/actions/runs/46085109098), artifact 15238447811 (SHA256 `26dc4d77ed7adc2860da248d4191eaf86bbd79a3072c9bc1e7b6a749fe81cdb0`). This is a *local* family result, not a Canonical40 reduction or BB(6) solution.

The single source file [Raw34ElevenSideCycles.lean](Raw34ElevenSideCycles.lean) defines the exact literal four-instruction parent, eleven distinct seven-hole D1 children, and eleven finite right-half-line recurrence witnesses. Original-source Lean accepts `all_never`: **all full completions of each child diverge**, with only standard axioms. The certified children are `0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC`. The precise witness quadruples, proof, original-source runner, and 25-way gap are recorded in the [research result](../../results/2026-11-27-raw34-eleven-infinite-rays-agent50.md).

A JS discovery-only depth-two search using the same partial table, finite side-cycle equality and canonical first-introduction filter found 85 candidate side-cycle terminal leaves, 120 unresolved leaves, two longer growth patterns and 24 state-introduction aliases at cutoff 200, with 10 internal splits. These exploratory counts are **not Lean results**, not a complete parent classifier, and must not be promoted without source-accepted exact partition and leaf proofs. The candidate growth children are:
`1RB---_1RC---_0RD0LC_1LC1RD_------_------` and
`1RB---_1RC---_0RD1LC_1LC1RD_------_------`.

Further discovery should focus on closing remaining first-hole children and consuming only a **complete parent** or exact residual subtree on the current Canonical40 chain. Avoid recounting the 11 already accepted infinite rays.
