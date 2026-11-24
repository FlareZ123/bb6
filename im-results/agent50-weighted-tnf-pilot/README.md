# Authentic weighted-TNF pilot

A complete normalized subtree at cut 6, reached from `firstOneCylinder` by nine genuine first-hole refinements, has an exact local weighted threshold of 84 by the explicit finite-replay argument below. [TNFPilot.lean](TNFPilot.lean) constructs the actual `FirstHolePath` and `WeightedTNFCertificate` proof objects using the unmodified source interfaces. **Full original-source compilation passed** in [manual run 45405148454](https://github.com/FlareZ123/bb6/actions/runs/45405148454), at commit `20db4dbe086ea0e6436eacbb5fab725957d3bda2`; the dedicated step ran successfully, including the standalone replay and fail-hard axiom-output guard against `sorryAx` and `native_decide`. This is an intermediate integration pilot, not a universal BB(6) bound.

## Closing the executable residual frontier

[RootFrontier.lean](RootFrontier.lean) retains all 24 ordinary branches at every ancestor, charges the first-hole halter with its incoming delay, and proves every completion is either bounded or compatible with an explicit open leaf. The new `mem_residuals_iff` equates membership of the exact executable address/table list with the semantic open-leaf relation; `RootedFrontier.sound_of_residuals` consumes proofs of every listed residual. The nine-edge pilot has 207 off-path residual occurrences by the structural count (JSON: [root-frontier.json](root-frontier.json)). The generic soundness/disjointness theorems compiled in CI 45449667076 with standard axioms, but construction of the concrete pilot failed due to first-hole equality transport. The source repair restores the missing path validation theorem and transports the equality in both children. The generic list proofs and Boolean simplification pattern passed a minimal local Lean rc2 preflight; exact source acceptance of the repaired module remains pending the existing combined run.

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

[RecursiveResidual.lean](RecursiveResidual.lean) implements a recursive checked tree, including a deliberately open default, an exact halt-sibling weight check, last-hole shortcuts and directional-cycle certificates. [SideCycle.lean](SideCycle.lean) now has a single-pass prefix-window check for longer witnesses. The four DepthEightSiblingData modules cover the 17 still-open C1 sibling cylinders (265,625 raw completions) with 107 explicit residuals: 101 one-hole and 6 two-hole cylinders, total mass 6,275. The finite evidence found halters with at most 394 ordinary moves, so a conservative weighted bound is 400. Three complete sibling cylinders (indices 83, 120, 127) close without any open leaf. The remaining 259,350 raw completions are covered by candidate finite witnesses. [DepthEightSiblingCoverage.lean](DepthEightSiblingCoverage.lean) consumes the roster and retains any unmatched cylinder, yielding 231 root residual occurrences (deeper refinement increases the count but sharply decreases completion mass). Generic recursive soundness was locally preflighted; the full generated data and source integration are **not yet Lean-accepted**. No complete BB(6) proof is claimed.

The source-native Coq connection remains a separate obligation: SourceResidualRoster.v is a draft checker for exact parent containment, not an import of Lean proofs. The actual-source queue must be exhausted or shown covered by source-native certificates before the global upper theorem follows.
