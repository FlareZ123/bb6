# Four source-proved late-entry left-sidecycle nonhalting cylinders in Raw34

**Agent 40 — 28 November 2026.** Original-source, standard-axiom Lean proof accepted in [manual CI run 46142276152](https://github.com/FlareZ123/bb6/actions/runs/46142276152), theorem `BB6.Agent40Raw34FLongSideCycles.all_never`. This is a *local* BB(6) nonhalting classification, not a determination of BB(6).

## The result

Under the standard six-state, two-symbol convention, let `---` denote a free transition (including HALT as one possible completion). For **every** complete machine extending **any** of the following four partial transition tables, the run from the genuine entirely blank infinite tape never halts.

| Original physical partial machine | Certified recurrence entry | Period | Retained half-line |
| --- | ---: | ---: | --- |
| `1RB---_1RC---_0RD0LB_1LC0RF_------_1LF0LC` | 72 | 1 | left of +6 |
| `1RB---_1RC---_0RD1RD_1LC0RF_------_1LF0LC` | 64 | 1 | left of +6 |
| `1RB---_1RC---_0RD0RC_1LC0RF_------_1LD1LF` | 60 | 5 | left of +10 |
| `1RB---_1RC---_0RD0LF_1LC0RF_------_1RD0RD` | 60 | 3 | left of +11 |

The four tables fix the same original Raw34 instructions A0=1RB, B0=1RC, C0=0RD, D0=1LC and four additional instructions. Each has exactly four unrestricted physical transition slots. The cylinders are pairwise disjoint because their assigned C1/F0/F1 patterns conflict. Their **gross physical union** therefore contains exactly `4×25⁴ = 1,562,500` complete six-state tables, with one actual HALT action plus twenty-four ordinary moves per free slot. This is not the number newly absent from the repository's older proof bank: overlap against that bank needs exact subtraction.

## Mechanism and proof

The four original blank-start partial runs exhibit an oriented **leftward** translated-half-line recurrence only after 60–72 primitive steps. For each fixed witness, a positive-length verified segment returns to the same state, shifts the head one cell left, and agrees with the earlier finite tape after that shift on all cells at or left of the recorded boundary; the head remains on the retained half-line during that segment. The contents strictly to the right of the boundary are allowed to differ. Iterating the sound half-line recurrence guarantees arbitrarily long live runs regardless of all unspecified instructions, which can include HALT.

This *does not* assume that finding a periodic pattern in a finite simulator proves divergence. The exact **source checker** `BB6Coverage.Agent50SideCycle.fastSideCycleCheck` decides the local recurrence witness for each literal partial table using `finiteWindow` and `finiteTailEq`. Its independently proved soundness theorem `fastSideCycleCheck_sound` transfers this to `NeverHalts` for every compatible original machine. The source file `[Raw34FLongSideCycles.lean](../im-results/agent40-raw34-frontier/Raw34FLongSideCycles.lean)` contains the four original 12-slot coded tables, positive periods, literal half-line directions and boundaries, and a universal all-completions theorem. The CI log records `all_never` with **only** `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or `native_decide`.

## Why these differ from the earlier shallow side-cycle bank

The earlier deterministic F-sidecycle generator searched only entries below 60 and periods at most 30. These four examples have earliest found valid witnesses at entries 60, 64, or 72 in the extended search and were excluded from its 9,231 depth-four early-witness list. They lie among the **69 four-fixed-slot branches** that run for at least the first 100 queried steps without a stop or newly undefined instruction (a purely computational candidate-selection fact, not a proof). Extending the witness entry to 600 and period to 300 produced these four new genuine source certificates. Longer-running members of the other 65 branches remain research targets.

Reproduction: original-source Lean closure via manual `.github/workflows/agent23-raw34-halters.yml` mode `f-long` on commit `c761e3a1`, [run 46142276152](https://github.com/FlareZ123/bb6/actions/runs/46142276152), success. Accepted source transcript includes `'BB6.Agent40Raw34FLongSideCycles.checked'` and `'BB6.Agent40Raw34FLongSideCycles.all_never'`, with the standard axiom profile.

## Four additional E/F-conjugate original-state cylinders — independently source accepted

The same *original-source checker*, independently applied to each distinct E/F-swapped **physical** table, has now certified four further nonhalting cylinders:

| Additional E-branch partial table | Entry | Period | Retained half-line |
| --- | ---: | ---: | --- |
| `1RB---_1RC---_0RD0LB_1LC0RE_1LE0LC_------` | 72 | 1 | left of +6 |
| `1RB---_1RC---_0RD1RD_1LC0RE_1LE0LC_------` | 64 | 1 | left of +6 |
| `1RB---_1RC---_0RD0RC_1LC0RE_1LD1LE_------` | 60 | 5 | left of +10 |
| `1RB---_1RC---_0RD0LE_1LC0RE_1RD0RD_------` | 60 | 3 | left of +11 |

All four have **four** unrestricted original transitions, and D1=0RE instead of D1=0RF in the original four tables, so the eight certified physical cylinders are mutually disjoint. Their combined gross union has **8×25⁴ = 3,125,000** physical total completions.

The E variants are not merely assumed nonhalting because a prior F machine was nonhalting: the concrete source `[Raw34ELongSideCycles.lean](../im-results/agent40-raw34-frontier/Raw34ELongSideCycles.lean)` checks the four rewritten 12-slot original tables, entries, periods, directions and boundaries directly using the original finite-window decision procedure, then instantiates the same already source-proved all-time `fastSideCycleCheck_sound` theorem. [Source-closure run **46143551875**](https://github.com/FlareZ123/bb6/actions/runs/46143551875) independently compiled the original four **and** E-conjugate four, checked both `all_never` exports, excluded `sorryAx`/`native_decide`, and succeeded. The E-variant *fresh marginal* relative to the wider original source bank is not yet included in the 9,861-F-source count.

## Limits

These certificates do **not** prove a universal maximality bound for all six-state machines, close the Raw34 parent, or reduce the accepted Canonical39 global roster. They are all-time mathematical nonhalting results for the four stated subcylinders. Exact fresh mass relative to the current wider source bank is being computed separately in `im-results/`.
