# Agent48 side-cycle graft into the canonical 124-table first-one frontier

## Result under construction

This dossier composes two existing proof objects:

- Agent13's `canonicalResidualRoster_sound_395`, which covers the first-one root by a weighted bound of 395 or one of 124 exact residual tables;
- Agent47's `hasWitness_sound`, which proves a weighted bound of 7014 for any table exactly present among the 388 checked side-cycle witnesses.

Four of the 124 residuals have exact side-witness descendants. The corresponding first undefined rows are:

| Raw residual | Canonical index | Parent table | Split row | Exact side-witness actions |
|---:|---:|---|---|---|
| 8 | 4 | `1RB--- / 0LC---` | C/1 | 1, 2, 4, 8 |
| 9 | 5 | `1RB--- / 0RC---` | C/0 | 1, 2, 4, 5, 6, 8, 10, 12 |
| 10 | 6 | `1RB--- / 1LC---` | C/1 | 1 |
| 23 | 13 | `1RB--- / 1RC--- / 0LD---` | D/1 | 2, 4, 6, 8, 12 |

Action numbers are 1-based indices in Agent50's `allMoves` order (state-major, then write bit, then direction). Each listed side witness is exactly the child table obtained by assigning that action at the split row; these are not approximate or merely overlapping matches. The witness IDs in `SevenSideWitnesses.lean` are 4–7, 72–73 and 137–142, 180, and 251–255.

## Combined theorem

`Agent48RosterGraft.lean` defines a generic 25-way split (halt plus all 24 ordinary moves), filters out children recognized by Agent47's exact `hasWitness` predicate, and replaces the four parent tables.

The intended result is:

- 18 exact child cylinders discharged by Agent47's `hasWitness_sound`;
- 82 child cylinders retained as open residuals;
- 120 untouched residuals retained;
- a 202-table residual roster;
- every first-one-root completion is either `WeightedBound 7014` or compatible with one of those 202 residual tables.

The original 395 bound is weakened monotonically to 7014 so the two certificate families share one bound. `WeightedBound` is the repository's weighted score predicate, not a raw step-count statement.

## Validation status

The Lean module imports the exact Agent13 and Agent47 proof modules and prints axiom profiles for the combined coverage theorem and roster cardinality. It is intended to be compiled through the existing manual `agent13-coverage.yml` workflow under target `weighted-tnf-roster-agent47-graft`. Until that CI run succeeds, treat the combined theorem as unverified source, not an accepted result.

This graft does **not** decide the 202 remaining residual cylinders and does not establish the universal upper bound for BB(6). It is an exact, bounded reduction of one part of the global first-one frontier.
