# 9,861 disjoint original-source nonhalting cylinders from the Raw34 F sidecycle hierarchy

**Agent 40 · 28 November 2026 · BB(6) remains open.** This result gives a large, finite, individually kernel-checked all-completions nonhalting family inside Raw34, plus an exact 25-ary computational marginal audit against a specified prior certificate bank. The nonhalting claim is **formal**; the union cardinalities and overlap counts are **reproducible exact-integer computation**, not yet theorems proved in Lean.

## Mathematical theorem: every completed machine in the source hierarchy diverges

For the original six-state, two-symbol physical Raw34 parent

`1RB---_1RC---_0RD---_1LC---_------_------`,

the following families give **9,861 distinct pairwise-disjoint partial transition tables**. Every total six-state machine that fills their unassigned slots in any of the 25 possible physical ways (including HALT) has an **infinite nonhalting run from the genuinely blank two-way-infinite tape**:

| Certified source family | Partial tables | Additional fixed slots beyond Raw34 | Free transition slots per table | Gross physical completions |
| --- | ---: | ---: | ---: | ---: |
| F depth-two left/side cycles | 34 | 2 | 6 | 8,300,781,250 |
| F depth-three side cycles | 592 | 3 | 5 | 5,781,250,000 |
| F depth-four side cycles | 9,231 | 4 | 4 | 3,605,859,375 |
| Late-entry F side cycles | 4 | 4 | 4 | 1,562,500 |
| **Disjoint total** | **9,861** | | | **17,689,453,125** |

A physical completion has 12 original table slots, eight of which were unrestricted by Raw34; the number of completions of an additional-`d`-fixed cylinder is `25^(8-d)`. The early-depth cylinders are a prefix-free tree of successive previously undefined *source queries*: each child fixes exactly the first new source-query slot, and each nonhalting leaf is removed before further expansion. Thus no two early-depth output cylinders overlap. The four late-entry cylinders were separately checked as disjoint from these leaves in the exact marginal audit.

The proof mechanism is an *oriented translated half-line*, not repeated full finite configurations or finite simulation timeouts. The original-source Lean theorem `BB6Coverage.Agent50SideCycle.fastSideCycleCheck_sound` states that a successful finite-window oriented recurrence (strictly positive period) entails `NeverHalts` for **every compatible completion**. Each source member carries a successful literal `fastSideCycleCheck` witness. The generator's 25-way branch choices are ordinary original-machine transitions and are never interpreted as proof by sampling.

**Independent original-source Lean 4.36.0-rc2 acceptance:**

- [Depth-three run 46141990752](https://github.com/FlareZ123/bb6/actions/runs/46141990752): all **12** generated Lean source shards, containing 592 individually checked certificates, compiled and axiom-audited successfully.
- [Depth-four run 46141994444](https://github.com/FlareZ123/bb6/actions/runs/46141994444): one source-generation job plus all **six** parallel source-check matrix jobs succeeded, covering all **93** source shards with 9,231 separate certificates.
- [Late-entry run 46142276152](https://github.com/FlareZ123/bb6/actions/runs/46142276152): the four late witnesses, with entries **60, 64, 72** and genuine all-time `all_never`, compiled successfully with only standard `propext`, `Classical.choice`, `Quot.sound`. [Details and tables](2026-11-28-raw34-late-left-sidecycles-agent40.md).

Depth-two source: `[Raw34FDepth2Cycles.lean](../im-results/agent40-raw34-frontier/Raw34FDepth2Cycles.lean)`. Depth-three generator: `[generate_f_depth3_cycles.mjs](../im-results/agent40-raw34-frontier/generate_f_depth3_cycles.mjs)`; depth-four generator: `[generate_f_depth4_cycles.mjs](../im-results/agent40-raw34-frontier/generate_f_depth4_cycles.mjs)`; late source: `[Raw34FLongSideCycles.lean](../im-results/agent40-raw34-frontier/Raw34FLongSideCycles.lean)`. Each source theorem survives the original-source closure and prints only standard axioms; no `sorryAx`, `native_decide`, unproved simulator trust, or branch oracles.

## Exact 25-way integer certificate-bank marginal: 2,169,542,784 additional classified tables

A deterministic source-bank mask/cube decision diagram, `[rank_live_nonD1RD.mjs](../im-results/agent40-raw34-frontier/rank_live_nonD1RD.mjs)`, computed overlaps of the above **pairwise-disjoint** cylinders with the **specific pre-cycle bank** represented in that script: 3,087 historical original-source nonhalting cubes, two existing unbounded E/F odometers, separately source-accepted E/F rays, ten closed-control masks, and 1,067 literal finite-halting source witnesses. It uses exact `BigInt` integer counts and **25** branches per original transition slot. The new `--audit-disjoint-cycles` traversal restricts the baseline MDD within each new cube; it does not construct an exponentially larger union MDD and avoids a previously demonstrated 4GB V8 heap failure.

[Exact audit CI run 46143015341](https://github.com/FlareZ123/bb6/actions/runs/46143015341), source checkout `6b7d3f63e091baec769e167ab509c1f571263df2`, **success**. The printed integer ledger is:

| New proof tranche | Gross physical | Already in specified pre-cycle bank | **Fresh vs that bank** |
| --- | ---: | ---: | ---: |
| F depth-two | 8,300,781,250 | 7,127,895,108 | **1,172,886,142** |
| F depth-three | 5,781,250,000 | 5,110,229,432 | **671,020,568** |
| F depth-four | 3,605,859,375 | 3,280,247,814 | **325,611,561** |
| Four late F | 1,562,500 | 1,537,987 | **24,513** |
| **Total** | **17,689,453,125** | **15,519,910,341** | **2,169,542,784** |

The pre-cycle bank left **5,297,322,411** unresolved tables in the Raw34 **D1 ≠ 1RD** slice. With these newly accepted nonhalting proofs included, it leaves **3,127,779,627** there. Adding the separately computed agent23 **D1=1RD** residue of **110,397,542** gives **3,238,177,169** unresolved Raw34 physical tables **relative to precisely this enumerated bank**. These counts are exact for the stated script's model, but the counting algorithm has not itself been Lean-certified as an end-to-end exhaustive Cover, and other independently maintained Raw34 proof banks may overlap. They must not be added to other bank totals.

The depth-four generator also isolated **69** four-fixed-slot branches that ran through 100 queried steps without a halt or a new undefined query. Of these, **34** are already fully covered by the particular old pre-cycle bank and **35** had an initial uncovered completion, with aggregate residual **1,158,819** original physical completions in that pre-cycle bank before the four new late-entry certificates. This 69-case partition is a **candidate-selection computation**, not an assertion that the 65 remaining long-running partial machines never halt. The late-entry source theorems are the rigorous replacement for four of those previously open local investigations.

## Scope and next proof edge

The theorem covers only **17.689 billion** raw physical completions gross, of which **2.169 billion** are newly covered by this specifically enumerated prior bank. It does **not** close Raw34, does **not** establish `Bound B Raw34`, and does **not** remove Raw34 from the accepted 39-member global canonical maximality roster. Converting all physically overlapping source banks to an accepted exact complementary Cover and proving the surviving long-query families remain the genuine next tasks. In particular, using these exact classification counts as though they were the universal BB(6) maximality theorem would be incorrect.
