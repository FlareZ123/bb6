# Source-certified marked-return ray cylinders

**Status (6 November 2026):** Forty pairwise disjoint genuine blank-root nonhalting cylinders in the original six-state, two-symbol source model. Original unmodified source dependencies and [MarkedReturnSource.lean](MarkedReturnSource.lean) compiled successfully in [manual Lean CI 42304709471](https://github.com/FlareZ123/bb6/actions/runs/42304709471), job 128191002496. The certificates use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. This is an intermediate global coverage improvement, not a determination of any hard BB(6) holdout, universal upper bound, or exact BB(6).

## Exact physical theorem

Let `q` be any one of B,C,D,E,F, choose an initial direction `d`, and choose arbitrary write bits `u,v`. Fix just three state-symbol rules:

- `A/0 = (write 1, move d, q)`.
- `q/0 = (write u, move opposite d, q)`.
- `q/1 = (write v, move opposite d, q)`.

The other nine rules are arbitrary, including halts. Starting on the true blank tape, A marks the origin, moves into the fresh neighbor in state q, and q reads 0. That move reverses onto the marked origin, where q necessarily reads 1. The assigned q/1 move takes the head to the previously untouched cell in direction opposite d. From there q/0 advances into fresh zeros forever in the same direction; nothing else can be consulted. This is an infinite valid original-source run, independent of all nine omitted entries.

The [Lean theorem `markedReturn_source_cover`](MarkedReturnSource.lean) proves `Cover (DecidedBelow bound) (markedReturnTable q d u v)` for every parameter tuple in the exact forty-element list and for every natural bound. It invokes the original finite-support tape semantics and `finiteRayCheck_sound` after three *actual* steps, including the read-one step. The source check is kernel-evaluated (`by decide`) in `markedReturnParams_ray`; no post-reversal read-zero approximation is used.

## Mass and pairwise disjointness

There are exactly `5 * 2 * 2 * 2 = 40` tuples. Every sparse table fixes exactly three of the twelve independent machine input rows; hence it has exactly `25^9` compatible full tables. The theorem `markedReturnCases_mass` kernel-checks this for every listed table. The theorem `markedReturn_unique` proves that one full machine cannot extend two parameter-distinct tables: A/0 determines q and d, while the q/0 and q/1 rules determine u and v. The finite parameter list is proved length 40 with no duplicates. Thus the union contains exactly

```
40 * 25^9 = 152,587,890,625,000
```

of the `25^12 = 59,604,644,775,390,625` raw tables, or exactly 0.256% of the full space.

These forty cylinders are disjoint from Agent32's existing analytically enumerated 52.786874368% first-event Z-or-D class because the root transition writes one and q's read-zero transition immediately reverses. They are disjoint from the ten reversing-ray cylinders in [EntryControlAudit.lean](../agent32-zero-prefix-global/EntryControlAudit.lean) because those fix A/0 to write zero. Consequently the already justified 54.386874368% conservative family increases to **54.642874368%**, representing `32,569,691,162,109,375` distinct raw full machines, by an elementary disjoint union. The new material is contained in `im-results/` because this does not yet close any difficult root.

## Relationship to the broader six-zero-row census

The independent exhaustive C++ census in [Agent32's dossier](../agent32-zero-prefix-global/README.md) reports 143,060,975 classified assignments of the six read-zero input rows out of 244,140,625 (58.597775360% of raw full tables). This is a **different**, broader computational classification; the current repository does not yet have a kernel theorem equating that count with the complete Lean zero-row audit mass. For any zero-row assignment extending our fixed A/0 and q/0, the C++ classifier cannot recognize a pristine zero-write cycle, cannot recognize a closed fresh directed ray before the second step, and encounters the marked read-one slot at its next step. It therefore records that zero-row assignment as open. Thus the new class is disjoint from the C++-reported classification *as a predicate*, yielding a conditional combined computational count `35,079,583,740,234,375` raw machines (58.853775360%) if the C++ count is taken as accurate. This conditional numeric comparison is kept separate from the unconditional 54.642874368% combinatorial union above.

## Verification boundary and next task

CI [42304709471](https://github.com/FlareZ123/bb6/actions/runs/42304709471) checked exact theorem names `markedReturnParams_ray`, `markedReturn_source_cover`, `markedReturnCases_mass`, and `markedReturn_unique` against unchanged source modules. The pairwise witness semantics and each sparse-cylinder mass are source-proved. The closed-form union counting uses the certified length, uniqueness theorem, and elementary 25-way independent-completion combinatorics.

The highest-value follow-up is to compose this physical read-one branch into a global source-carrying residual-tree audit and connect it to an authentic unresolved root, rather than optimizing the raw-table percentage by adding more easy local patterns. A separate exact source-kernel equality for the broader six-zero-row census remains open.
