# Eighty-five source-certified infinite-ray cylinders in Raw34

**Status: unconditional original-source Lean theorem acceptance, two proof levels.** This is a new local universal nonhalting result, not a complete Raw34 parent Cover, not a reduction of the accepted Canonical40 global proof frontier, and not an exact BB(6) determination.

## Exact machines and result

The canonical Raw34 eight-hole parent specifies only

```
1RB---_1RC---_0RD---_1LC---_------_------
```

with state A initially scanning a blank zero tape. Its first undefined transition is D1 (at ordinary time 5). We prove nonhalting from blank for **85 disjoint partial-table cylinders** inside this parent, all over the standard 25-outcome-per-slot six-state, two-symbol Turing machine model. The theorem is universal over the unspecified transitions, including possible halting transitions in those slots; no empirical step limit is part of the mathematical conclusion.

The 85 cylinders consist of:

1. **Eleven entire D1 children**, each with D1 one ordinary transition fixed and seven other entries still free. The eleven fixed moves are `0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC`. The first-level theorem `BB6.Agent50Raw34Eleven.all_never` establishes `NeverHalts` for every full machine compatible with any corresponding child.
2. **Seventy-four second-level children** of nine different D1 branches. For each first D1 move, a blank-root trace fixes the next *actually queried* undefined slot; one of its 25 outcomes is fixed and six entries remain free. The theorem `BB6.Agent50Raw34Depth2.all_never` establishes `NeverHalts` for every compatible full machine in each of these 74 literal refinements. The exact 74 slot/move/witness instances are [machine-readable](../im-results/agent50-raw34-firsthole/depth2-candidate-witnesses.json) and [source-formalized](../im-results/agent50-raw34-firsthole/Raw34Depth2SideCycles.lean).

| First D1 move for second-level descendants | Actual next queried slot | Certified second-level children |
|---|---|---:|
| `0LD` | C1 | 8 |
| `0LE` | E0 | 9 |
| `0RE` | E0 | 14 |
| `1LA` | B1 | 8 |
| `1LB` | C1 | 9 |
| `1LD` | C1 | 8 |
| `1LE` | E0 | 1 |
| `1RD` | C1 | 7 |
| `1RE` | E0 | 10 |
| **Total** | | **74** |

The first-level D1 transition values are pairwise distinct; none of the 74 second-level witnesses uses a first-level move already settled by the eleven-parent theorem. The 74 second-level pair keys `(D1 transition, actual second slot, second transition)` are pairwise distinct, and the slot is constant for each D1 value as shown above. Consequently all 85 cylinders are physically disjoint. Their combined exact count is

\[
11\cdot25^7+74\cdot25^6=85\,205\,078\,125
\]

different total physical transition tables. (This is a cardinality of a certified subset of the Raw34 cylinder, *not* the Busy Beaver enumeration or the number of halting tables in all six-state machines.) The full Raw34 parent has `25^8 = 152,587,890,625` completions; the remainder is not all resolved.

## Why the proofs establish infinite computation, not long simulation

Each witness consists of a blank-root entry time, a strictly positive return period, an orientation (right/left), and a retained half-line boundary. The finite original-source checker `fastSideCycleCheck` establishes that the execution within the period stays on its designated half-line and that the ending configuration matches the starting configuration there, after an oriented nonnegative head translation. The cells behind the retained boundary can change arbitrarily. The source-proved `BB6Coverage.Agent50SideCycle.fastSideCycleCheck_sound` uses this relation and arbitrary-iteration induction to show that the machine executes at least `n*k` more steps for every natural `k`, and therefore cannot halt.

The first-level witnesses have entry 0–4 and periods 2–6, all right-oriented. The 74 depth-two witnesses have entry at most 31, periods at most 9, and include both right- and left-oriented cycles. All 85 finite checks are performed *inside Lean* against the literal partial transitions. The witness discovery script/JSON is not trusted by the theorem.

## Kernel acceptance, axiom profile and exact reproduction

- **First-level source:** [Raw34ElevenSideCycles.lean](../im-results/agent50-raw34-firsthole/Raw34ElevenSideCycles.lean), `BB6.Agent50Raw34Eleven.all_never`; accepted in [original-source CI run 46085109098](https://github.com/FlareZ123/bb6/actions/runs/46085109098), artifact [15238447811](https://github.com/FlareZ123/bb6/actions/runs/46085109098/artifacts/15238447811), zip SHA256 `26dc4d77ed7adc2860da248d4191eaf86bbd79a3072c9bc1e7b6a749fe81cdb0`.
- **Second-level source:** [Raw34Depth2SideCycles.lean](../im-results/agent50-raw34-firsthole/Raw34Depth2SideCycles.lean), `BB6.Agent50Raw34Depth2.all_never`, `pairwise_key_distinct`, `separate_from_first_level`; accepted in [original-source CI run 46085429345](https://github.com/FlareZ123/bb6/actions/runs/46085429345), artifact [15238832709](https://github.com/FlareZ123/bb6/actions/runs/46085429345/artifacts/15238832709), zip SHA256 `b3d9e42368b8761de64ee5a2b157ad97b4afd7dc9f275854a2921054a46944e1`.

Lean **4.36.0-rc2** compiled 9 project modules for the first level and all 10 project modules for the second level from pinned sources. The exported `all_never` proof at both levels depends only on the standard `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `native_decide` or extra oracle occurs. The strict CI source runner has options `raw34-sidecycle` and `raw34-depth2` within the existing [Agent50 manual workflow](../.github/workflows/agent50-raw47-lifted.yml).

## Missing universal proof obligations

The corresponding bounded depth-two discovery enumerated 120 unresolved canonical leaves and two longer tape-growth candidates after the 85 side-cycle cases and 24 state-introduction aliases. These counts are **only reproducible search observations**, not an accepted exact Lean partition or universal bound. The two longer candidates are the partial tables `1RB---_1RC---_0RD0LC_1LC1RD_------_------` and `1RB---_1RC---_0RD1LC_1LC1RD_------_------`. They display persistent growth through the discovery cutoff but have **no all-time nonhalting proof** yet. A full Raw34 parent Cover requires a source-certified exhaustive partition consuming the genuinely remaining cases, including state-introduction equivalents, actual halt branches, and these growth children.

The present theorem rules out halting in 85 precisely defined subfamilies, regardless of other seven/six table slots. This makes a useful formal reduction for later Raw34 parent closure, but does not discharge a single current global Canonical40 representative until its entire Cover or an accepted refinement of the global residual theorem is formally constructed.
