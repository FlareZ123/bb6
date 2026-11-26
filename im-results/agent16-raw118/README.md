# Raw118: sharp candidate parent bound and complete certificate roster

**Parent:** `1RB---_1RC---_0RD---_1LD1RE_---0LE_------`, E1 = 0LE, raw frontier index 118. **Status:** every discovery leaf now has a candidate proof, including the final M2869 nonhalting holdout (locally checked against original source by Agent 1). The unconditional parent theorem is not yet source-accepted. The sharp candidate weighted score is **756,496**, including the final halting query. This is a local cylinder, not a BB(6) upper bound.

## Exact parent obligation

The intended exported theorem is `BB6.Agent1Raw118Complete.parent_cover : Cover (WeightedBound 756496) parent` in [Raw118Complete.lean](Raw118Complete.lean). Its `parent_exact` additionally states that every universal weighted cover of this parent has bound at least 756496. The parent assembly is separate from the discovery search: the generated `Raw118Consumer` accounts for all 959 residual tables via exact literal table checks and 958 candidate certificates plus the explicit M2869 holdout; Raw118Complete consumes its independent nonhalting proof.

The [current source assembly run](https://github.com/FlareZ123/bb6/actions/runs/45736775052) reuses the complete sparse proof artifact and the wide-window proofs. The exact parent theorem and standard-axiom profile must pass before it is reported as established.

## Partition and certificate composition

The first-hole tree from Agent2's raw99 enumerator (1000 steps; translated-cycle window 256) partitions 25^6 = 244,140,625 physical completions:

| Class | Physical mass |
|---|---:|
| Translated cycles | 227,709,700 |
| Halt | 14,492,552 |
| Last-slot ordinary | 906,048 |
| Open | 1,032,325 |

Tree census: 7,424 splits, 126,916 cycle nodes, 37,752 last-hole nodes, 6,085 open leaves. Initial maximum weighted halt score 992. These discovery counts are not by themselves a kernel proof.

After FAR and short delayed-first-hole checks the partial audit has 959 residuals:

- 679 sparse n-gram leaves: the twelve-shard proof build and join in [45706919905](https://github.com/FlareZ123/bb6/actions/runs/45706919905) produced complete artifact **15067230828**, named `raw118-sparse-complete`, and source artifact **15065113250**. The overall run did not complete its final parent job; the sparse join artifact is reusable.
- 6 long delayed-first-hole leaves: [generate_late_traces.py](generate_late_traces.py) emits packed primitive-step proof modules. The largest leaf 439 has separate original-source acceptance.
- 274 hard leaves: 187 disjoint base certificates (105 symbolic, 10 independent-counter, 48 phase-graph, 14 recursive-counter, 6 BiDFA, 4 phase-aware TreeBiDFA), plus tree-bank, SAT, 47 wide-window, 20 run-summary, 4 nested-restoration, crossbank 3970 and compact 3981/4188/4197 macro certificates. The exact set complement is leaf 2869. The generators check index disjointness, the literal table strings, and the complete residual partition; Lean checks the actual table and proof before using any certificate.

The sparse and wide artifact routes avoid repeating expensive searches. [45667306290](https://github.com/FlareZ123/bb6/actions/runs/45667306290) is the principal wide run; [45672887654](https://github.com/FlareZ123/bb6/actions/runs/45672887654) supplies repaired 5180, 5187 and 5368 artifacts. The earlier accounted-core run [45707787943](https://github.com/FlareZ123/bb6/actions/runs/45707787943) failed because generated slot symbols were numeral 0/1 rather than Bool; current `generate_late_traces.py` emits false/true. The earlier full retry [45724552937](https://github.com/FlareZ123/bb6/actions/runs/45724552937) was cancelled, not a mathematical counterexample.

## Sharp attaining witness

Open index 439: `1RB1LE_1RC---_0RD1RA_1LD1RE_0LF0LE_1RF0RC`. Its first undefined query is B1 after 756,495 ordinary transitions. Filling B1 with halt gives the exact candidate score 756,496; its weighted delay includes zero. [PackedSweep.lean](PackedSweep.lean) and [generate_trace.py](generate_trace.py) prove the packed zipper refinement and the 6,803-instruction replay. Original-source CI [45575655393](https://github.com/FlareZ123/bb6/actions/runs/45575655393) accepted the late query and weighted last-hole certificate. [Raw118Sharp.lean](Raw118Sharp.lean) composes this witness with the parent subtable and proves the lower inequality for every parent Cover; its new full-parent source audit is part of the current assembly.

## All-time hard-leaf mechanisms

The hard-set proofs use inductive invariants, not a runtime cutoff. Four nested-restoration examples:

| Leaf | Source | Original-source CI | Mechanism |
|---|---|---|---|
| 655 | [Raw118Nested655.lean](Raw118Nested655.lean) | [45685852382](https://github.com/FlareZ123/bb6/actions/runs/45685852382) | F-section nested induction with right word `0 1^(n+1)` |
| 657 | [Raw118Nested657.lean](Raw118Nested657.lean) | [45686057730](https://github.com/FlareZ123/bb6/actions/runs/45686057730) | F-section nested induction with right word `(01)^(n+1)` |
| 10 | [Raw118Nested10.lean](Raw118Nested10.lean) | [45687301172](https://github.com/FlareZ123/bb6/actions/runs/45687301172) | Two-phase strong induction restoring left zero gaps |
| 434 | [Raw118Nested434.lean](Raw118Nested434.lean) | [45688897136](https://github.com/FlareZ123/bb6/actions/runs/45688897136) | Six-digit carry language with arbitrary suffix and padding |

The previously final holdout M2869 is `1RB0LB_1RC0RA_0RD0RF_1LD1RE_1LB0LE_1RA---`. Agent1's [four-module proof and reproduction dossier](../agent1-raw118-macro/README.md) proves `BB6Coverage.Agent1Raw118M2869.never` using 18 arbitrary-tail macros, a 53-step blank entry and a finite phase-aware token-stack abstraction. The local original-source Lean check reports only propext and Quot.sound. Raw118Complete matches that exact literal table before consuming the theorem. No further M2869 search is needed.

The other source-audited mechanisms and original run IDs are preserved in the [pre-consolidation detailed dossier at 68dd11c7](https://github.com/FlareZ123/bb6/blob/68dd11c7dd7809a8d8876cbf4dd1f29562346911/im-results/agent16-raw118/README.md) and the [Agent40 independent-counter dossier](../agent40-raw118-independent/README.md). That historical version's pending statuses are superseded by the status above.

## Exact quotient handoff

[Raw118CanonicalCut.lean](Raw118CanonicalCut.lean) is **source-accepted, conditional on the Raw118 Cover**. It supplies a generic quotient-roster cut from a sharp local Cover and an existing sound roster, preserving every other entry. The specific 68-to-67 count and exact target theorem passed original-source Lean compilation in [45737177344](https://github.com/FlareZ123/bb6/actions/runs/45737177344), reusing the already audited 68/74/76/77 objects. The proof artifact is `15079342035`. This theorem does not discharge the Raw118 Cover or the other parent/roster obligations. Once the local parent is source-accepted, apply the generic cut to the then-current accepted roster, checking exact membership and its complement. The binding score floor 6,766,859 from Raw110 is unchanged.

## Reproduction and remaining acceptance gate

`discover.py` regenerates the enumeration and candidate partitions. Newline-terminated `open.txt` SHA256: `00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9`. Tree JSON SHA256: `3d6425a04241b88e96a79f6ebc523592ad64b391cc114597e57831454291d8b5`. Use `generate_partial.py`, `emit_consumer.py --accounted`, [ResidualAccounted.lean](ResidualAccounted.lean) and [emit_accounted.py](emit_accounted.py) for the in-place subtree accounting proof. The existing manual workflow `agent13-coverage.yml` has target `weighted-tnf-raw118-consumer` with inputs `raw118_sparse_run_id=45706919905`, `raw118_wide_run_id=45667306290`, `raw118_wide_repair_run_id=45672887654`. Its conditional cut target is `weighted-tnf-raw118-canonical-cut`.

Next gate: finish the original-source unconditional parent Cover and exact-score audit. If it succeeds, consume it in the strongest accepted canonical roster. No global BB(6) conclusion is asserted.


## 26 November 2026 update: parent Cover remains open; Canonical64 is the current base

The generic conditional cut in [Raw118CanonicalCut.lean](Raw118CanonicalCut.lean) was source-accepted in [run 45737177344](https://github.com/FlareZ123/bb6/actions/runs/45737177344), artifact 15079342035. It proves the roster-cut composition conditionally on a Raw118 parent Cover; it does **not** establish that Cover.

The full parent assembly [run 45736775052](https://github.com/FlareZ123/bb6/actions/runs/45736775052) was cancelled at 02:35:44Z and uploaded no artifacts. Therefore Raw118 remains an open parent, despite the accepted generic cut. Do not report Raw118 as closed from run 45737177344.

The strongest accepted base is now the [Canonical64 Raw120 integration](../../results/2026-11-26-canonical64-raw120-integrated-agent3.md), source-accepted in [run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590), artifact 15085029091. Raw118 can be applied to that exact roster once its parent Cover passes: prove the unique Raw118 membership in Canonical64, use the generic sound cut, and compose on whichever 63-residual parent cut is accepted first (Raw112 or Raw59). Avoid presenting competing 63-residual frontiers.
