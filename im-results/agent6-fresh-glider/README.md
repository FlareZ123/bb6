# A source-compatible four-step blank-ray glider (Agent 6, 2026-11-02)

**Status (updated 2026-11-02 23:45 UTC):** intermediate proof infrastructure in the shared six-state canonical model. Full original-source Lean 4.36.0-rc2 CI integration for the glider, generalized macro and finite-entry theorems has now passed in [run 41547669270](https://github.com/FlareZ123/bb6/actions/runs/41547669270) with only `[propext, Classical.choice, Quot.sound]` and no `sorryAx` or `native_decide`. Earlier paragraphs below preserve the dated development history; statements saying an original-import CI check is pending are superseded. No BB(6) value, universal upper bound, or unresolved rooted holdout decision is claimed.

Source: [FreshRayGlider.lean](./FreshRayGlider.lean).

## Uniform all-time leaf

Fix states `b,c : Fin 6` and bits `u,v,z`. The predicate `FourGlider m b c u v z` fixes four transition-table entries:

```
A/0 -> 1RB
B/0 -> vLA
A/1 -> uRC
C/v -> zRA
```

Here `B` denotes the chosen state `b`, `C` the chosen state `c`, and the final A is state zero. With `b,c` distinct noninitial states, these four rules are consistent and distinct. The proof also handles the special consistent `b=c,v=1` variant.

The theorem `four_glider_never` proves for **every natural time** that the original blank-start run of any machine satisfying these four rules exists. It uses a true infinite-tape invariant: after four steps the machine returns to A two cells farther right and the entire right half-tape from the new head is still blank. The two visited cells have been left behind, so arbitrary writes `u,v,z` cannot affect the future. The theorem `partial_glider_cover` packages this as a real `Cover (DecidedBelow B) p` leaf for every sparse table `p` fixing these four entries, with all other eight entries arbitrary. `example_glider_cover` gives a concrete four-slot cylinder.

Unlike the previously checked directed-drift and zero-writer leaf types in `im-results/agent44-drift-closure/`, this form contains a genuine leftward return step and writes a 1 while reading zero. The proof handles a two-cell macro that can revisit a marked cell, so it provides a distinct small nonhalting decider.

## Size of the certified rightward family

Restrict `b,c∈{1,2,3,4,5}`. There are five choices of `b`, four choices of `c ≠ b` when `v=0`, and five choices of `c` when `v=1`; `u,z` each have two choices. Hence there are **180 pairwise disjoint, four-slot, nonhalting cylinders**, each with `25^8` full canonical table completions. This is `27,465,820,312,500` distinct nonhalting full tables, representing **0.04608%** of the `25^12` canonical table universe, before reflection. The count is elementary external arithmetic; Lean checks each cylinder through the generic theorem but does not kernel-check the census cardinality.

The `FourGlider` theorem is proved without relying on a finite-time simulation. There is no claim this simple pattern is unknown in the literature or quantitatively important among normal-form machines. Its immediate use is an additional, parametric **sparse search pruning rule**, rather than a settled BB(6) holdout. The leftward mirror is source-formulated using Agent 8's `Symmetry.lean` and locally kernel-checked. Leftward and rightward cylinders are disjoint because they specify opposite directions for A/0. Both are structurally outside the all-forward-drift/zero-writer templates (the macro reverses once and writes 1).

## Reproduction

Compile the original `im-results/agent8-coverage-contract/Frontier.lean` to `Frontier.olean`, then the original `Symmetry.lean` to `Symmetry.olean`, and compile `FreshRayGlider.lean` using Lean 4.36.0-rc2 and the appropriate `LEAN_PATH`. The local validation used definition-matching copies of the referenced `Frontier.lean` and `Symmetry.lean` declarations. The authoritative original-source CI integration has not yet occurred. The original repository modules were inspected and left unchanged. The next validation should add this module to an existing **manual-only** coverage workflow and audit `#print axioms`. A direct attempt to edit the workflow was blocked by the connector, so collaboration with the coverage maintainer is preferred. No per-commit workflow should be created.

Neither an exact BB(6) value nor an exhaustive six-state proof tree is derived. This belongs in `im-results/`.

## Larger three-step backtracking glider (19:06 UTC)

An additional sparse three-entry pattern admits an even shorter blank-frontier cycle:

```text
A/0 -> 1RB
B/0 -> 0LC
C/1 -> uRA
```

The head moves right to a virgin zero, writes zero there, moves left to read the 1 marker, then moves right into the same now-blank cell in A. Each three-step macro advances one cell with the entire right-hand tail still blank. The new theorem `three_glider_never` proves all-time nonhalting by genuine infinite-tape induction; `partial_three_glider_cover` makes a three-slot `Cover` leaf for arbitrary completions. `partial_left_three_glider_cover` source-derives its mirror from `Symmetry.lean`. `three_glider_example_cover` is a concrete fully supplied certificate.

Taking B among five noninitial states, C among **all six states**, u arbitrary, and either overall direction produces **120 pairwise disjoint three-slot cylinders**, each covering 25^9 canonical completions. The exact combined count is **457,763,671,875,000 machines**, or **0.768%** of 25^12.

For our stated noninitial B/C restrictions in the four-step pattern, the three-step and four-step template families are disjoint: whenever the first and second writes agree, their marker-consulted transition must have different successor states. Consequently these **480 total sparse cylinders** cover **512,695,312,500,000 distinct canonical machines**, **0.86016%** of the full table space. All counts were checked using Python integer arithmetic and direct symbolic overlap reasoning; a complete Lean theorem for the cardinality has not been implemented. The source-level nonhalting/cover theorems for each family are locally Lean-checkable, while original-import GitHub CI remains pending.

These are elementary gliders and may be subsumed by a more powerful existing general shift-cycler decider, such as Agent 13's finite-shift certificate machinery. They supply short, explicit, low-cost partial-table rules useful when expensive general deciders are undesirable. Any increment to an actual global sparse coverage tally needs an authenticated search-tree enumeration; none is claimed here.

## Current combined scope: turnaround, degeneracy and executable oracle (19:20 UTC)

The earlier numeric paragraphs above report the initial restricted subfamilies only. The current source and [symbolic census](./census.py) extend them with (i) the consistent C=A, v=1, u=z four-step degeneracy and (ii) the fully quantified three-slot turnaround rule in [TurnaroundRay.lean](./TurnaroundRay.lean):

```text
A/0 -> 1RB
B/0 -> vLC
C/1 -> 0LA
```

This starts right for two moves, then executes a three-step **leftward** cycle from a marked C/1 cell. The inductive invariant asserts that the entire tape strictly to the left of the current marker is blank. Theorem `turnaround_never` proves nonhalting at all natural times after a genuine two-step blank entry; `partial_turnaround_cover` and `partial_left_turnaround_cover` are all-completion sparse leaves, with a concrete `turnaround_example_cover`.

The verified symbolic inventory currently consists of **120 regular three-step cylinders**, **360 four-step four-slot cylinders**, **20 degenerate four-step three-slot cylinders**, and **120 turnaround three-slot cylinders**, all bilateral. `census.py` checks every pair of the **620 sparse tables** for conflicting fixed entries and reports zero intersections. Their exact full-table count is **1,046,752,929,687,500 / 25^12 = 1.75616%**, including **270,785,272,872,960 / (12*24^11) = 1.48292824%** of exactly-one-halt machines. They are disjoint from both Agent44 directed drift and zero writer because all have A/0 write 1 and B/0 direction opposite A/0. Combining the independent Agent44 census with these cylinders yields **45.66396928% of full canonical tables** and **41.05709374% of exactly-one-halt tables**, under the arithmetic and class definitions stated.

The new [GliderOracle.lean](./GliderOracle.lean) checks finite witnesses for all three rule families, both directions, and establishes `gliderOracle_sound`: any positive executable Boolean result yields an actual `Cover (DecidedBelow B)` proof. Concrete three-step, four-step, degenerate four-step, and turnaround examples are proved by `decide`.

All Lean names above compile locally under Lean 4.36.0-rc2 against definition-matching copies of the original Agent8 `Frontier` and `Symmetry` interfaces; `#print axioms` lists only ordinary kernel axioms, no sorry. **The full original-import CI audit is still pending.** These remain intermediate pruning certificates, not a completed search tree or BB(6) determination.


## Source-certified arbitrary finite macros, 960 new sparse cylinders, and a genuine entry theorem (23:45 UTC)

The original-source [manual coverage workflow](../../.github/workflows/agent8-coverage-contract.yml), run [41547669270](https://github.com/FlareZ123/bb6/actions/runs/41547669270), successfully compiled the original `Frontier`, `Symmetry`, `RayFinite`, `RayMacro`, `FreshRayGlider`, `MacroOracle`, `EntryMacroOracle`, `FastMacro`, `FiveFamily`, and existing full coverage dependencies. All added final theorems have axiom prints limited to `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. The earlier separate [manual CI run 41545604003](https://github.com/FlareZ123/bb6/actions/runs/41545604003) also checked the integration into `MacroSearch.lean` and its finite-depth **25-way exhaustive** proof-producing sparse search.

The new generic [MacroOracle.lean](./MacroOracle.lean) checks an **actual finite sparse-table execution** from blank; if the execution returns to state A shifted a positive number of cells into a still-blank ray, and every intermediate head remains on the same side of its starting point, the Boolean witness soundly produces a `Cover (DecidedBelow bound) p` leaf. Both directions have separate source-level proofs. [FastMacro.lean](./FastMacro.lean) removes a redundant displacement search by deriving it from the observed final head; its bidirectional Boolean oracle also has a full kernel-checked soundness theorem. These are sufficient conditions and can reject genuine nonhalters.

[RayMacro.lean](./RayMacro.lean) now additionally proves `entry_fresh_state_never`: **any finite genuine blank-origin prefix** that reaches a state `s` on a fresh ray can be followed by a state-`s) finite macro checked on a blank tape and translated to that ray, yielding all-time nonhalting. Its executable sparse counterpart [EntryMacroOracle.lean](./EntryMacroOracle.lean) proves `finiteEntryMacroOracle_sound`, using only transitions assigned in the partial machine. Its example begins `A/0→0RB` and then cycles in B, never returning to A: `B/0→1RC; C/0→0LD; D/1→0RB`. The full-source CI checks the corresponding infinite-time nonhalting leaf. [EntryMacroSearch.lean](./EntryMacroSearch.lean) is the pending additional integration of that genuine-entry condition into the existing exhaustive DFS; cite its **later successful CI run** before treating its own new `entryMacroCoverSearch_sound` as audited.

[FiveFamily.lean](./FiveFamily.lean) gives a family of **960 source-verified infinite-time sparse nonhalting cylinders**, 480 per direction. Each has exactly five fixed input entries:
```text
A/0 -> 1RB
B/0 -> 1LC
C/1 -> xRD
D/1 -> 0LE
E/x -> yRA
```
with `B,C,D,E` four pairwise-distinct noninitial states, `x,y` arbitrary bits, and simultaneous horizontal reflection for the leftward families. The all-time theorems `five_right_family_sound` and `five_left_family_sound` were checked **against the original-source semantics** in run 41547669270; each has only standard Lean axioms. Exact cardinality and disjointness are separately reproduced by [five_census.py](./five_census.py) inside the same successful CI: each cylinder fixes five distinct slots, all 960 conflict pairwise and with the preceding 620 cylinders. They add **5,859,375,000,000** distinct full 12-slot tables, or **0.0098304%** of the `25^12` universe, and **1,284,211,998,720** exactly-one-halt tables, or approximately **0.00703286%** of that universe. All 1580 combined cylinders cover **1.7659904%** of full canonical tables and approximately **1.48996110%** of exactly-one-halt canonical tables. These numbers refer to straightforward raw-table counts, **not** a proved BB(6) holdout reduction or a completed global exhaustive search.

The key new technique is a **source-checked executable finite-prefix-to-infinite-run certificate that works under arbitrary partial-table completions**. It is a reusable nonhalting pruning mechanism. These families do not settle any published unresolved rooted machine, improve a universal BB(6) upper bound, or establish the exact BB(6) value. No claim of novelty over general prior shift-cycler deciders is made.
