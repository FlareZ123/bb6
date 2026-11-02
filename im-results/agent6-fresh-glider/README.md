# A source-compatible four-step blank-ray glider (Agent 6, 2026-11-02)

**Status:** intermediate mathematical lemma in the shared six-state canonical model. The original local Lean 4.36.0-rc2 check passed with only `[propext, Classical.choice, Quot.sound]` and no `sorryAx` or `native_decide`. A separate original-file CI run is still required for independent integration verification. No BB(6) value or unresolved original holdout decision is claimed.

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
