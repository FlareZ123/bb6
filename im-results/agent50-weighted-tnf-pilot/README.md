# Authentic weighted-TNF pilot

A complete normalized subtree at cut 6, reached from `firstOneCylinder` by nine genuine first-hole refinements, has an exact local weighted threshold of 84 by the explicit finite-replay argument below. [TNFPilot.lean](TNFPilot.lean) constructs the actual `FirstHolePath` and `WeightedTNFCertificate` proof objects using the unmodified source interfaces. **Full original-source compilation passed** in [manual run 45405148454](https://github.com/FlareZ123/bb6/actions/runs/45405148454), at commit `20db4dbe086ea0e6436eacbb5fab725957d3bda2`; the dedicated step ran successfully, including the standalone replay and fail-hard axiom-output guard against `sorryAx` and `native_decide`. This is an intermediate integration pilot, not a universal BB(6) bound.

## Closing the executable residual frontier

[RootFrontier.lean](RootFrontier.lean) retains all 24 ordinary branches at every ancestor, charges the first-hole halter with its incoming delay, and proves every completion is either bounded or compatible with an explicit open leaf. The new `mem_residuals_iff` equates membership of the exact executable address/table list with the semantic open-leaf relation; `RootedFrontier.sound_of_residuals` consumes proofs of every listed residual. The nine-edge pilot has 207 off-path residual occurrences by the structural count (JSON: [root-frontier.json](root-frontier.json)). The generic soundness/disjointness theorems compiled in CI 45449667076 with standard axioms, but construction of the concrete pilot failed due to first-hole equality transport. The source repair restores the missing path validation theorem and transports the equality in both children. The generic list proofs and Boolean simplification pattern passed a minimal local Lean rc2 preflight; exact source acceptance of the repaired module remains pending the existing combined run.



## Exact source checkpoint / canonical residual cross-match

The deterministic script [q32-canonical-crossmatch.js](q32-canonical-crossmatch.js) compares the 84 literal tables in `Agent8PackedChunk2_32_32.v` with all 124 tables in `canonical-124.json`, using twelve-slot pointwise refinement (a parent hole is a wildcard). It finds that **all 84 queue tables refine exactly one canonical parent: index 7**, and none refines any of the other 123. This parent is raw residual index 11, with address `B0=1RC, C0=0LA`, depth 2, nine holes, and table `1RB---_1RC---_0LA---_------_------_------`. The row order is the source encoding `A0,A1,B0,B1,...,F0,F1`; `Agent32SourceEncoding.agent32_table_roundtrip` gives the source string's pointwise roundtrip, while the canonical JSON records the corresponding packed table.

This is an exact finite data cross-match, **not yet a source-accepted containment theorem and not a safety proof**. The same replay parses the 32 literal `SWside` certificate tables and the two exact sweep tables in `Agent47SourceChunk2.v` / `Agent47SourceSweep.v`: together they cover 34 of the 84 queue nodes, leaving 50. The 50 residuals have hole histogram `{3: 9, 4: 3, 5: 6, 6: 10, 7: 22}` and none has exactly one hole, so the current last-hole cylinder constructor cannot close any of them directly; the next reduction must find more side-cycle certificates or split residuals at an earlier first hole. Agent 48's separate 388-witness cross-match found no compatible side-witness extension of canonical residual 7. The q_i(2,32), 32-update checkpoint therefore isolates one especially important open nine-hole cylinder. Agent 44 has been asked to include the 84-to-index-7 relation in the canonical string-to-`TM` bridge.

A deterministic blank-tape simulation in the same replay script finds the first undefined row of **all 50** residuals within 18 ordinary transitions. The first-hole-time histogram is `{5: 15, 6: 4, 7: 8, 8: 8, 9: 1, 11: 5, 12: 8, 18: 1}`; the first-hole slot histogram is `{E0: 11, F0: 4, E1: 9, C1: 11, B1: 9, D1: 2, D0: 4}`. This supplies candidate `(n,h)` data for the source-native `source_hole_atb` checker. If checked, a `source_first_hole_split` at each residual would discharge its halting branch with weighted bound at most `18 + 6 = 24`; the 24 ordinary children per split still require certificates or further splits. This is therefore a promising shallow split frontier, not a completed closure.

The focused Coq `enumerate62-source-roster` target has been run repeatedly to remove concrete upstream blockers. The original run [45487107741](https://github.com/FlareZ123/bb6/actions/runs/45487107741) failed at `Agent8SourceWF.v:202`; subsequent repairs now get `Agent8SourceWF.v` through its old/fresh child expansion and membership lemmas. The latest run [45496042119](https://github.com/FlareZ123/bb6/actions/runs/45496042119) now fails at `Agent8WeightedSource.v:17`: the TC62 executable multistep result is not definitionally convertible to the original `Individual62` machine/configuration types, and the available TC62 `multistep_c_spec` only supplies relational-run-to-executable direction. A converse execution-to-relation lemma or explicit transport is still needed. The build has therefore **not yet reached** `SourceResidualRoster.v` or the Agent47/44 consumer; none of the source-roster claims above is Coq-accepted yet. Agent 8 has the exact diagnostic and a suggested induction/transport route.
The direct Coq source-queue programme has a distinct proof boundary: Lean proofs cannot be imported directly into Rocq. [SourceResidualRoster.v](SourceResidualRoster.v) proposes a finite twelve-slot containment checker, with a soundness/completeness theorem against actual `is_child_of`, monotone source-weighted cylinder safety, source-native nonhalting and last-hole leaf constructors, and a roster-based consumer for `actual_source_global_upper`. A certified parent may cover any more refined queue residual; exact string equality or disjointness of the parent roster is unnecessary. The last-hole theorem counts the final halt query and at most five incoming zero writes, using totality for ordinary fills. This is a **source-level draft** until the pinned Coq dependency closure and this module compile. It does not transfer the Lean certificates, prove a complete roster, or decide BB(6). The next integration is to add this module to the existing weighted-source target after Agent8's dependencies compile, then supply actual source-native roster proofs and exact checkpoint matches. Local Coq is unavailable; Lean rc2 works, but direct git checkout fails DNS.

## Certificate

Parent table: `1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_0LE0LA`.

The authentic path (ordinary moves, queried slot, assigned action) is:

| moves | slot | action |
|---:|---|---|
|1|B0|1RC|
|2|C0|0RD|
|3|D0|1LD|
|5|D1|1RE|
|6|E1|0LB|
|7|B1|1LF|
|8|F1|0LA|
|11|C1|0RB|
|21|F0|0LE|

All six labels are introduced in canonical order. The first hole at the parent is A1 at time 31, head -1 and ones {-1,1,3,4,6}. The halt sibling has raw score 32, with possible incoming delays [0,1,2], so weighted score at most 34. The other hole is E0.

Every ordinary A1 branch has one of the following certificates. A last-hole witness is the time of its first E0 query; E0=halt scores n+1 and the other 24 E0 assignments are total ordinary tables. A ray witness reaches D with an entirely blank left half-line and D0=1LD. A lasso repeats the exact state, absolute head, and finite tape set.

| A1 | verdict | time | earlier repeat |
|---|---|---:|---:|
|0LA|last|36| |
|0LB|last|40| |
|0LC|ray|33| |
|0LD|ray|32| |
|0LE|last|32| |
|0LF|last|33| |
|0RA|lasso|40|20|
|0RB|lasso|52|20|
|0RC|last|34| |
|0RD|ray|32| |
|0RE|last|32| |
|0RF|last|33| |
|1LA|last|83| |
|1LB|last|68| |
|1LC|last|34| |
|1LD|ray|32| |
|1LE|last|32| |
|1LF|last|33| |
|1RA|lasso|33|29|
|1RB|lasso|36|20|
|1RC|last|34| |
|1RD|last|37| |
|1RE|last|32| |
|1RF|last|42| |

The 16 last-hole halters all set E0=halt, which excludes every nonzero incoming zero-prefix delay: no read-zero row can lead to A. Thus their exact weighted scores equal their raw scores; the maximum is 84 (A1=1LA, E0=halt). There are 625 raw completions in the parent cylinder: 25 from A1=halt, 16 last-hole halters, and 584 nonhalters (16×24 + 8×25). No residual child is discarded. The full branch has one expand node, 16 lastHole nodes and eight nonhalt nodes. The 25 root-halt completions are handled by the expand weight proof.

## Reproduction and acceptance

Run `python replay.py` in this directory to independently replay the authentic path, every witness, and the exact incoming-delay sets. The script checks finite evidence, not Lean proofs. The Lean module uses kernel `decide` for the same finite predicates and the repository's existing sound last-hole, lasso, ray and weighted-TNF rules. Its exact source closure compiled under Lean 4.36.0-rc2 through the existing manual coverage workflow's `weighted-tnf-pilot` target. The module prints the axiom profiles of all six principal exported declarations, and the workflow rejects `sorryAx` or `native_decide` in the captured compilation output. The successful-job log itself was not retrieved, so the precise printed profile beyond that guard is not independently asserted.

The source checkout failed locally with DNS resolution of github.com, although the uploaded Lean 4.36.0-rc2 toolchain extracted and ran successfully. The existing manual closure runner provided the accepted original-source check; no new standalone workflow was created. The entire root-to-parent path's other siblings remain outside this pilot. It is a genuine local integration slice, not a closed authentic root or the full upstream queue schedule.


## Larger authentic subtrees bordering three pinned Cryptids leaves

The half-line checker in [SideCycle.lean](SideCycle.lean) proves recurrence from a finite observation in either direction. It retains all cells on one side of a fixed boundary, checks every consulted position lies on that side, and checks the translated end configuration agrees throughout that half-line. All earlier abandoned cells may differ. Its induction constructs arbitrarily long runs, so this is an actual nonhalting argument for every compatible completion, not a finite cutoff.

[CryptidSiblings.lean](CryptidSiblings.lean) checks authentic first-hole paths and all ordinary children except the explicitly designated already-proved hard leaf, then assembles a complete weighted certificate given that leaf. The r2 and r6 source closures passed [45406543043](https://github.com/FlareZ123/bb6/actions/runs/45406543043) at `8d4bd6830649cb0b9c5b1a04c66d3d4415a3632d`. [CryptidGraft.lean](CryptidGraft.lean) imports the pinned nonhalting leaves and checks pointwise equality of the actual designated tables. Combined pinned-source run [45406904998](https://github.com/FlareZ123/bb6/actions/runs/45406904998) is pending at this checkpoint.

| Parent | First hole, ordinary time | Last-hole / half-line / growth / pinned branches | Exact local weighted bound (conditional on graft acceptance) |
|---|---|---|---:|
| `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB---_---1RA` | E1, 35 | 6 / 17 / 0 / 1 | 471 |
| `1RB1RA_1RC---_0LD0RA_1RF1LE_---1LF_1LC0LF` | B1, 62 | 7 / 16 / 0 / 1 | 582 |
| `1RB0RA_0RC0LE_1LD1RF_1LB---_1LD1LE_---1RA` | D1, 38 | 9 / 13 / 1 / 1 | 1768 |

The r3 new proof uses [SparseZipper.lean](SparseZipper.lean) and [R3Sweep.lean](R3Sweep.lean). For the D1=1LB sibling, at the right blank boundary let the head be h and the tape to its left be the physical word (110)^(2n), with all other cells blank. A macro of 32+32n ordinary moves reaches the same form with n+1 and head h+2. The proof decomposes the macro into a five-step prelude, n six-step pair transfers left, a 27-step turnaround, and n 26-step pair transfers right. The zipper bridge proves it simulates the repository's ordinary sparse machine. The source-independent local Lean checks passed with only propext and Quot.sound; actual source closure run [45408170628](https://github.com/FlareZ123/bb6/actions/runs/45408170628) is pending. The r3 pinned leaf graft will be added after this check.

These are distinct cut-six parents (each contains 625 total transition tables under the repository's 25-choice raw completion convention). They do not by themselves prove that the original upstream queue enumeration reaches these parents without an earlier decider pruning the route, nor close the other subtrees at the root.

## November 24: exact residual reduction and alternating sweeps

The root pilot now has a proof-free, ordered enumeration of its 207 residual cylinders with exact twelve-slot pack/unpack; the exported JSON and executable enumeration agree entry-for-entry in an independent JS replay. RootFrontier.lean adds residual-list soundness and a finite certificate roster checked against exact tables. No hash is a proof premise.

**New inductive result:** [AlternatingResidualSweep.lean](AlternatingResidualSweep.lean) covers two F0 variants (0LB and 1LD), and [AlternatingVariants.lean](AlternatingVariants.lean) covers 17 ordinary descendants of seven additional F0 siblings. All share the family A on a blank cell, with blank tape to its left and (01)^m immediately to its right. Nine ordinary moves from blank reach m=2, and a macro sends m=2n+2 to m+2, shifting the head one cell left. The 17-variant proof consumes two leftward alternating blocks at a time. Its atom identities hold with arbitrary tape tails by reduction, and its sweep recurrence holds by induction. The complete operational recurrence was checked locally in Lean 4.36.0-rc2 against copied exact SparseZipper definitions; the source-level nonhalting transfer still awaits full dependency compilation.

The proposed root certificate now handles all 24 F0 ordinary assignments and the F0 halt branch at the depth-eight cylinder. Ten direct nonhalting siblings, thirteen two-hole sibling trees, and the original pilot close the 15,625 raw completions at weighted bound 92. The 91-ordinary-move witness uses F0=1RA, A1=0LF, E0=halt; its score including the halt query is 92. Across the root path, 53 direct nonhalting leaves and 13 two-hole subtrees reduce 207 residual occurrences to 141, with threshold raised from 84 to 92. These counts and witnesses are independently replayed candidate results; full source CI is running at [45456488584](https://github.com/FlareZ123/bb6/actions/runs/45456488584). The proof declarations remain drafts until accepted.

[RecursiveResidual.lean](RecursiveResidual.lean) implements a recursive checked tree, including a deliberately open default, an exact halt-sibling weight check, last-hole shortcuts and directional-cycle certificates. [SideCycle.lean](SideCycle.lean) now has a single-pass prefix-window check for longer witnesses. The four DepthEightSiblingData modules cover the 17 still-open C1 sibling cylinders (265,625 raw completions) with 107 pre-FAR explicit residuals: 101 one-hole and 6 two-hole cylinders, total mass 6,275. The finite evidence found halters with at most 394 ordinary moves, so a conservative weighted bound is 400. Three complete sibling cylinders (indices 83, 120, 127) close without any open leaf; the existing tree certificates cover 259,350 raw completions. [DepthEightSiblingCoverage.lean](DepthEightSiblingCoverage.lean) now imports the four independently checked FAR leaves `p85_0`, `p114_0`, `p116_0`, and `p128_0`, proves their exact membership in the raw sibling residual roster, and filters only exact packed-table matches. The kernel-checked post-FAR open roster has 103 leaves (97 one-hole and 6 two-hole), raw mass 6,175; the existing growth witnesses then discharge the six two-hole leaves, leaving `siblingFinalRoster_count = 97` and mass 2,425. At the root, `refinedRootRoster_count` falls from 231 to 227 and the post-growth `finalRootRoster_count` from 225 to 221. The integration and soundness/axiom checks passed Lean 4.36.0-rc2 CI [run 45523629756](https://github.com/FlareZ123/bb6/actions/runs/45523629756), with only standard axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx` or `native_decide`. This remains an intermediate subtree: 97 one-hole leaves are still open, and the source-native queue connection/global upper bound is not established. No complete BB(6) proof is claimed.

The source-native Coq connection remains a separate obligation: SourceResidualRoster.v is a draft checker for exact parent containment, not an import of Lean proofs. The actual-source queue must be exhausted or shown covered by source-native certificates before the global upper theorem follows.


## 2026-11-25: source-native q32 parent tree attempt (Coq verification pending)

The earlier 84-node cross-match identifies canonical residual 7 as the unique canonical parent of the `q_i(2,32)` checkpoint. The 50 residuals left after the existing 34 source certificates are only one active queue slice of that parent cylinder. To address the whole parent, not just that slice, `Agent50Q32ParentTreeSearch.v` constructs a source-native tree beginning at the parent’s first undefined row `(A,S1)` after three ordinary moves.

The reusable builder `agent50_bounded_source_tree depth p` tries the complete existing translated-cycler candidate grid on the exact supplied TM; if no side certificate is found, it searches first undefined rows at times 0–18 and splits into all 24 ordinary children, recursively to the requested depth. Its structural theorem `agent50_bounded_source_tree_checked` proves that every generated tree passes `source_tree_check` for every partial table and every depth whenever the weighted bound is at least 24. This proof uses the actual candidate predicate on the same table checked by the tree, plus a proved 0–18 first-hole time bound; it does not infer safety from search failure.

The q32 parent instance uses depth 1 at bound 7014. Its exact open leaves are filtered against the already checked `chunk_roster` (34 original-source certificates). The larger 50-parent side-search roster is deliberately omitted from this focused target to avoid recompiling that expensive search; it can be added as a later coverage layer if needed. The conditional theorem `agent50_q32_parent_safe_from_open_uncovered` proves that safety of the remaining uncovered leaves implies `source_table_safe 7014 q32_canonical_residual_7`. The file prints the open-leaf count and a small table-string sample. This is a source-checked conditional closure theorem, **not yet an unconditional closure**: the remaining list must be empty or separately proved safe.

The manual `enumerate62-source-first-hole` target in `.github/workflows/shared-rocq-root-proofs.yml` now copies and compiles this q32 tree module after `Agent8Chunk2FirstHole.vo`. The shared `Agent47SourceTree.v` dependency was repaired at commit `099dff49`: it now uses `Agent47TC.Flip.Compute.cmultistep` and transports the translated run with `translated_multistep_transfer`, matching the established proof in `Agent47SourceWitness.v`. The old source-roster run `45518968407` was dispatched on pre-repair commit `ee808a25` and was still in progress at the last checkpoint; it is not evidence for the repaired tree.

A separate full-grid search over the unique serialized strings of all 1,200 first-hole children from the 50 residuals is preserved in `Agent50Chunk2ChildSideSearch.v`. It proves a conditional frontier theorem for the q32(2,32) checkpoint, but is deliberately not included in the first q32-parent CI target because its search is substantially larger. The parent-level 24-way tree is the first priority.

No BB(6) upper bound or exact value follows until the source-tree target compiles and every remaining open leaf is closed. The source-tree data, checker, and conditional theorem are reproducible in the cited Coq module.


## Experimental translated-cycler bridge — not proof-accepted

`TranslatedCycler.lean` is an unfinished attempt to replay the source
`verify_tcycler_r` witness format using `SourceFiniteSemantics.lean`.
It is **not currently a trusted dependency**. A CI compilation that pulled
this module (run
[45554609301](https://github.com/FlareZ123/bb6/actions/runs/45554609301))
reported unresolved goals and invalid indexed-induction cases, and its
`#print axioms` output included `sorryAx` for
`translatedCyclerCheck_sound` and `sampleSourceLeaf`. Do not use any
theorem from this file as a certified nonhalting result until the module
compiles cleanly and the axiom audit contains no `sorryAx`.

The new raw10 lasso below deliberately avoids this module. It uses the
already-existing `LeafRules` prefix-agreement and exact-cycle theorems
directly.

## 2026-11-25: raw10 B0=1LC two-hole lasso cylinder

`Raw10Box8Cycle.lean` defines the partial table with row
`[8,14,11,0,17,4,9,2,23,15,10,0]` in
`Raw10Encoded` slot order
`A0,A1,B0,B1,C0,C1,D0,D1,E0,E1,F0,F1` (zero denotes an unassigned
slot). It fixes ten transitions and leaves exactly B1 and F1 unassigned;
`holes_exact` checks this in Lean.

From blank tape, the default completion reaches state D at head zero after
24 ordinary moves, with ones exactly at positions -3, -2, and 1. Fourteen
more moves return to the identical state, absolute head, and full tape.
The return period reads
`D0,C0,E1,D1,A1,D0,C0,E0,F0,C1,A0,B0,C1,A1`; neither B1 nor F1 is
consulted. `Raw10Box8Cycle.lean` uses
`common_prefix_of_partial_table` to transfer the checked entry and period
to every completion, then `eventually_cycle_never` and
`WeightedTNFCertificate.nonhalt` to certify all 25^2 = 625 completions.

`Raw10Box8CycleConsumer.lean` adds this cylinder to the existing 65
side-witness tables and held table. It proves an exact characterization of
the new remainder and pairwise disjointness of its boxes, and exposes a
conditional score-B consumer. The condition still requires the held leaf,
all remaining 40 rectangles, and all other canonical residuals; this is
not an unconditional raw10 closure or a BB(6) upper bound.

An exact JS replay of the existing `subtractMany` partition algorithm
gives 40 residual rectangles and remaining mass 90,890,091,604,350 after
adding the new cylinder, versus 34 rectangles and mass 90,890,091,604,975
before it. The mass reduction is exactly 625. This count/mass calculation
is a reproducible finite computation, not yet a Lean cardinality theorem.

The dedicated manual CI target
`weighted-tnf-raw10-box8-cycle` compiles the consumer and its dependency
closure. Run
[45556817579](https://github.com/FlareZ123/bb6/actions/runs/45556817579)
was queued at commit `dfb0a16f8a8cff5cfcdb1a448e3f10421e6e2274`;
kernel acceptance is pending at this checkpoint.
