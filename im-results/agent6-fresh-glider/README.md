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

The `FourGlider` theorem is proved without relying on a finite-time simulation. There is no claim this simple pattern is unknown in the literature or quantitatively important among normal-form machines. Its immediate use is an additional, parametric **sparse search pruning rule**, rather than a settled BB(6) holdout. A mirror variant via the existing `Symmetry.lean` theorem could double this full-table coverage, subject to source verification.

## Reproduction

Load the original `im-results/agent8-coverage-contract/Frontier.lean` module as Lean's `Frontier` import and then compile `FreshRayGlider.lean` using Lean 4.36.0-rc2. The local validation used a definition-for-definition copy of the relevant `Frontier.lean` types; the full original source has been inspected and is unchanged. The next validation should add this module to an existing **manual-only** coverage workflow and audit `#print axioms`. No per-commit workflow should be created.

Neither an exact BB(6) value nor an exhaustive six-state proof tree is derived. This belongs in `im-results/`.
