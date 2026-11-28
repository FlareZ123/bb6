# Raw34 first-hole and depth-two infinite-ray certificates

**Current accepted result:** exactly **85 distinct oriented half-line infinite-ray cylinders**, containing `11*25^7+74*25^6=85,205,078,125` physical six-state two-symbol transition tables. This is a local universal nonhalting result, **not** a complete Raw34 Cover, a global Canonical40 reduction or BB(6) determination.

The true raw34 parent is `1RB---_1RC---_0RD---_1LC---_------_------`.

- [First level](Raw34ElevenSideCycles.lean): 11 ordinary D1 moves covered without any additional instruction; theorem `BB6.Agent50Raw34Eleven.all_never`. Original-source Lean [run 46085109098](https://github.com/FlareZ123/bb6/actions/runs/46085109098), artifact 15238447811; 9 project modules, standard axioms only.
- [Second level](Raw34Depth2SideCycles.lean): 74 additional D1/next-queried-slot move pairs; theorem `BB6.Agent50Raw34Depth2.all_never` with `pairwise_key_distinct` and `separate_from_first_level`. Original-source Lean [run 46085429345](https://github.com/FlareZ123/bb6/actions/runs/46085429345), artifact 15238832709; 10 modules, standard axioms only. The [full exact source data and the still open frontier](depth2-candidate-witnesses.json) may be inspected or used to resume discovery.

The common [SideCycle soundness theorem](../agent50-weighted-tnf-pilot/SideCycle.lean) turns these finite checks into universal nonhalting, including arbitrary untouched tape tails. All theorem axioms are confined to `propext, Classical.choice, Quot.sound`. The earlier [11-cylinder result](../../results/2026-11-27-raw34-eightyfive-infinite-rays-agent50.md) was extended in place to cover both source-accepted levels.

A discovery-only depth-two enumerator found 120 open canonical leaf boxes, two longer growing leaves, 24 state-introduction aliases, and ten splitting nodes after the 85 side-cycle closures. The two growth candidates are `1RB---_1RC---_0RD0LC_1LC1RD_------_------` and `1RB---_1RC---_0RD1LC_1LC1RD_------_------`. These are not proved nonhalting. The next decisive tasks are all-time proofs for growth cases, then certification of the exact local remainder and a complete parent or conditional global consumption interface.
