# Agent48 adaptive side-cycle graft into the canonical first-one frontier

## Mathematical input

This dossier composes two existing proof objects:

- Agent13's `canonicalResidualRoster_sound_395`, covering the first-one root by weighted bound 395 or one of 124 exact residual tables;
- Agent47's `hasWitness_sound`, proving weighted bound 7014 for any table exactly recognized by the 388 checked side-cycle witnesses.

Four of the 124 residuals have compatible side-witness extensions. Their first undefined rows are:

| Raw residual | Canonical index | Parent table | First split row |
|---:|---:|---|---|
| 8 | 4 | `1RB--- / 0LC---` | C/1 |
| 9 | 5 | `1RB--- / 0RC---` | C/0 |
| 10 | 6 | `1RB--- / 1LC---` | C/1 |
| 23 | 13 | `1RB--- / 1RC--- / 0LD---` | D/1 |

The adaptive tree then splits only partial children that still have exact side-witness descendants. Action numbers below are 1-based indices in Agent50's `allMoves` order (state-major, then write bit, then direction).

| Parent | Split path (row=action) |
|---:|---|
| 8 | C/1; if 15, D/0; if 5, C/0; if 12, D/1 |
| 9 | C/0; if 3, B/1; if 13, D/1; if 15, D/0 |
| 10 | C/1; if 13, D/0; if 11, C/0; if 17, E/0 |
| 23 | D/1; if 19, E/1; if 5, E/0; if 15, C/1; also if E/1=23, F/0; if 11, D/0 |

The Lean file defines all 18 internal split nodes as explicit refinements and proves that each split row is unassigned.

## Combined theorem

`Agent48RosterGraft.lean` uses a generic 25-way split (halt plus all 24 ordinary moves), filters out children recognized by Agent47's exact `hasWitness` predicate, and replaces the four parent tables.

The depth-four adaptive tree yields:

- 18 internal split nodes;
- 115 exact child cylinders discharged by Agent47's `hasWitness_sound`;
- 321 open leaves from the four affected parent cylinders;
- 120 untouched residual cylinders;
- a 441-table residual roster;
- every first-one-root completion is either `WeightedBound 7014` or compatible with one of those 441 residual tables.

The original 395 bound is weakened monotonically to 7014 so the two certificate families share one bound. `WeightedBound` is the repository's weighted score predicate, not a raw step-count statement.

A direct exact overlap count for the 388 side-witness family gives 52,665,776,340,625 covered completions across the four parent cylinders. The depth-four disjoint safe leaves capture 52,658,388,671,875 of them; the remaining overlap is 7,387,668,750 completions. These are finite combinatorial counts, not a claim that the remaining machines are decided.

## Dependency structure

The side-witness data/checker is factored into `SideWitnessCore.lean`, which imports only `RootFrontier` and `SideCycle`. `SevenSideWitnesses.lean` remains the public wrapper for the original seven-parent roster theorem and imports both `SevenRoster` and `SideWitnessCore`. This avoids pulling unrelated `Cryptids.Machines` dependencies into the 124-roster graft.

## Validation status

The combined theorem and exact list cardinalities are in Lean source and are intended to be compiled through the existing manual `agent13-coverage.yml` target `weighted-tnf-roster-agent47-graft`. The first compile exposed a local proof-script issue in `splitChildren_cover`; the proof was corrected and the target is being rerun. Until that CI run succeeds, treat the combined theorem as unverified source, not an accepted result.

This graft does **not** decide the 441 remaining residual cylinders and does not establish the universal upper bound for BB(6). It is an exact reduction of the first-one frontier using already checked side-cycle certificates.
