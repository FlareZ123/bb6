# Raw118: sharp candidate parent bound and complete certificate roster

**Parent:** `1RB---_1RC---_0RD---_1LD1RE_---0LE_------`, E1 = 0LE, raw frontier index 118. **Status:** the 958 nonhalting residual certificates and the exact M2869 holdout proof are assembled as a candidate parent Cover, but the unconditional parent theorem is not yet source-accepted. The sharp local weighted score is **756,496**, including the final halting query. This is one local cylinder, not a BB(6) upper bound.

## Exact parent obligation

The intended exported theorem is `BB6.Agent1Raw118Complete.parent_cover : Cover (WeightedBound 756496) parent` in [Raw118Complete.lean](Raw118Complete.lean). Its `parent_exact` additionally states that every universal weighted cover of this parent has bound at least 756496. The parent assembly is separate from the discovery search: the generated `Raw118Consumer` accounts for all 959 residual tables via exact literal table checks and 958 candidate certificates plus the explicit M2869 holdout; Raw118Complete consumes its independent nonhalting proof.

The first full assembly run [45736775052](https://github.com/FlareZ123/bb6/actions/runs/45736775052) was cancelled at its 60-minute job timeout. The focused rerun [45758026627](https://github.com/FlareZ123/bb6/actions/runs/45758026627) was cancelled at the 90-minute parent-job timeout while the generated proof closure was still compiling (the last observed module was `Raw118NodeRoot_23_07_02`). Setup, artifact downloads and Lean installation succeeded; no Lean diagnostic or parent-proof artifact was produced. This is a resource-budget failure, not a mathematical counterexample. The 180-minute retry [45768921666](https://github.com/FlareZ123/bb6/actions/runs/45768921666) completed source preparation and uploaded checkpoint artifact [15093576212](https://github.com/FlareZ123/bb6/actions/runs/45768921666/artifacts/15093576212), but its parent-assembly job failed while compiling generated `Raw118CloseRoot_*` shards. The first diagnostics are name-resolution errors: the generator emitted an unqualified `parent` while each shard opens `Agent31ThreeHole`, `Agent50TNFPilot`, and `Agent16Raw118`. This is an assembly-generator defect, not a counterexample or a failed mathematical certificate. The repair qualifies the initial root as `BB6.Agent16Raw118.parent`; rerun the existing `weighted-tnf-raw118-consumer` target with the same pinned sparse and wide artifacts. Raw118 remains open until `parent_cover` and `parent_exact` pass the original-source and standard-axiom audits.

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

The sparse and wide artifact routes avoid repeating expensive searches. Wide run [45667306290](https://github.com/FlareZ123/bb6/actions/runs/45667306290) was cancelled overall but preserved 44 successful, source-checked leaf artifacts; repair run [45672887654](https://github.com/FlareZ123/bb6/actions/runs/45672887654) succeeded with the remaining three (5180, 5187, 5368). All 47 were downloaded and reused by both parent runs 45758026627 and 45768921666; the same pinned inputs are preserved for the extended retry. The two focused run-aware batches also passed: [45675655736](https://github.com/FlareZ123/bb6/actions/runs/45675655736) for 14 leaves and [45676449188](https://github.com/FlareZ123/bb6/actions/runs/45676449188) for six leaves. The earlier accounted-core run [45707787943](https://github.com/FlareZ123/bb6/actions/runs/45707787943) failed because generated slot symbols were numeral 0/1 rather than Bool; current `generate_late_traces.py` emits false/true. The earlier full retry [45724552937](https://github.com/FlareZ123/bb6/actions/runs/45724552937) was cancelled, not a mathematical counterexample.

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


## 26 November 2026 update: Raw118 parent Cover source-accepted; Canonical64 remains the current base

The generic conditional cut in [Raw118CanonicalCut.lean](Raw118CanonicalCut.lean) was source-accepted in [run 45737177344](https://github.com/FlareZ123/bb6/actions/runs/45737177344), artifact 15079342035. It proves the roster-cut composition conditionally on a Raw118 parent Cover; it does **not** establish that Cover.

The first full parent assembly [45736775052](https://github.com/FlareZ123/bb6/actions/runs/45736775052) was cancelled at 02:35:44Z; the focused rerun [45758026627](https://github.com/FlareZ123/bb6/actions/runs/45758026627) reached its 90-minute timeout while compiling the generated closure, with no Lean diagnostic. The 180-minute retry [45768921666](https://github.com/FlareZ123/bb6/actions/runs/45768921666) ended in failure but preserved generated-input artifact [15093576212](https://github.com/FlareZ123/bb6/actions/runs/45768921666/artifacts/15093576212); the failed-job log endpoint did not expose a diagnostic, so this is not evidence against the certificates. The next full attempt [45790736514](https://github.com/FlareZ123/bb6/actions/runs/45790736514) successfully compiled all 24 generated `Raw118CloseRoot_*` modules, then failed in the final generated `Raw118Consumer.lean`: `parent` and `parent_root` were ambiguous among Agent31ThreeHole, Agent50TNFPilot and Agent16Raw118. The generated theorem declarations consequently carried `sorryAx`; no certificate counterexample was reported. Its generated-input artifact [15103075786](https://github.com/FlareZ123/bb6/actions/runs/45790736514/artifacts/15103075786) is preserved.

The source repair in commit `b2e050ea75b4633f06ce836375a4260135ed500c` fully qualifies the Raw118 parent/root/nohalt/bound in `emit_accounted.py` and the parent/holdout references in `Raw118Complete.lean`. The corrected existing-target retry [45812415227](https://github.com/FlareZ123/bb6/actions/runs/45812415227) **completed successfully**. Job `raw118_parent_assembly` passed the complete original-source Lean closure and configured standard-axiom audit; both `BB6.Agent1Raw118Complete.parent_cover` and `BB6.Agent1Raw118Complete.parent_exact` are source-accepted. The exact local parent bound is **756,496**. Preserved artifacts: [`raw118-parent-proof`, ID 15120592642](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15120592642), 531,464,312 bytes, SHA-256 `226a16e1181a456a2f6eddfb785b3882abde05d462837fffcb4b3ba47dfe2053`; [`raw118-parent-consumer`, ID 15119854660](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15119854660), 29,252 bytes, SHA-256 `8455d416e926d405c834448f32c1e11b1a46a460f74bd362ff85ae0583658b41`; and [generated inputs, ID 15113732668](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15113732668), 273,840,139 bytes, SHA-256 `ce913fcf8e8bf8c877e4342b22676b6970ac805aef54dcb4e3035f48bb9a3b19`. The earlier conditional cut run 45737177344 is not a parent Cover. Raw118's local parent Cover is now accepted, but Raw118 remains in the 64-entry global frontier until its Canonical64 membership helper and combined direct-from-Canonical64 consumer pass.

The strongest accepted base is the [Canonical64 Raw120 integration](../../results/2026-11-26-canonical64-raw120-integrated-agent3.md), source-accepted in [run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590), artifact 15085029091. The canonical-124 manifest identifies Raw118 as canonical index 82 (raw residual 118), with address B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=0LE. The draft helper proves the unique sameTable membership in Canonical64, but still needs source-closure compilation. With the Raw118 parent Cover now accepted, Agent31 should compose this local cut into the then-current accepted Canonical64-derived roster, including the already accepted Raw58 parent and any later accepted Raw57, Raw112, Raw59 or other parent cuts. Agent4's Raw112+Raw58 Canonical62 draft remains provisional until the Raw112 source/axiom gate passes. Do not publish a parallel 63-residual interface.


## Canonical64 membership helper (draft; not source-accepted)

Added [Raw118Canonical64Membership.lean](Raw118Canonical64Membership.lean) as a narrow integration helper. It proves the conditional-cut parent is definitionally equal to the Raw118 parent covered by Raw118Complete, and asks Lean to compute its exact unique sameTable membership in the accepted Canonical64 Raw120 roster. It deliberately defines no replacement roster and proves no new global soundness theorem. The file is **not yet source-accepted**; Agent31's existing Canonical64 source-closure workflow must compile and axiom-audit it alongside the accepted Canonical64 dependency closure. The parent Cover itself is now source-accepted in run 45812415227; only this membership helper and the combined consumer remain open.


## Canonical62 membership helper (draft; not source-accepted)

Agent4's current `Canonical62Raw112Raw58Integrated.lean` draft removes Raw112 and Raw58 together from Canonical64. The companion [Raw118Canonical62Membership.lean](Raw118Canonical62Membership.lean) imports that draft and Raw118Base only, using Raw118Base.parent directly as the parent covered by Raw118Complete, with exactly one sameTable occurrence in Agent4's `roster62`. It defines no roster or global soundness theorem. This helper is not source-accepted until Agent4's existing Canonical62 assembly workflow compiles and axiom-audits it. Agent4 confirms that the final coordinated reduction should be built directly from Canonical64 with one parent list [p112,p58,p118,p57], not by chaining provisional Canonical62/61 rosters. The Canonical62 helper is only a cross-check against the current [p112,p58] draft; the Canonical64 helper is the final membership proof needed for the direct 60-entry construction. No separate Canonical61/60 routes should be published.


## Accepted source-closure artifacts

The full Raw118 parent proof is source-accepted in [run 45812415227](https://github.com/FlareZ123/bb6/actions/runs/45812415227), pinned to source revision `b2e050ea75b4633f06ce836375a4260135ed500c`. The successful original-source closure and axiom audit produced the full [`raw118-parent-proof` artifact 15120592642](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15120592642) and [`raw118-parent-consumer` artifact 15119854660](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15119854660). The earlier generated-input checkpoint [15113732668](https://github.com/FlareZ123/bb6/actions/runs/45812415227/artifacts/15113732668) is retained for reproducibility; no sharded recovery is needed for this successful run.

Next gate: source-check `Raw118Canonical64Membership.lean` against the accepted Canonical64 dependency closure, then include Raw118 in Agent31's single direct-from-Canonical64 parent list. Until that combined consumer passes, the 64-entry global conditional frontier is unchanged and BB(6) remains unsolved.
