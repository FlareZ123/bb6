# #429: one authentic-root physical branch in the global BB(6) coverage scanner

**Scope and verification (6 November 2026).** This dossier records a literal, physically executed sparse-branch route of six-state machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` in Agent 32's genuine tape-based `firstUnknownPhysical` scanner. The source-check workflow is [agent1-429-physical-frontier](../../.github/workflows/agent1-429-physical-frontier.yml), whose corrected proof and all 22 exact-time checks **passed** the original shared-source Lean 4.36.0-rc2 verification in [run 42311918661](https://github.com/FlareZ123/bb6/actions/runs/42311918661). The earlier run 42311268028 failed only on missing a finite universal decidability instance and was corrected with explicit exhaustive finite-state cases. **This does not decide #429 or BB(6).**

## Actual sparse-branch path

The machine begins at state A on a physically blank tape. The input entries first consulted are:

| First raw-move index | State/read symbol | Exact source-table action |
| ---: | --- | --- |
| 0 | A/0 | `1RB` |
| 1 | B/0 | `1RC` |
| 2 | C/0 | `0RD` |
| 3 | D/0 | `1LE` |
| 4 | E/0 | `0LA` |
| 5 | A/1 | `0LF` |
| 6 | F/1 | `1LA` |
| 8 | B/1 | `1RA` |
| 11 | C/1 | `0RB` |
| 17 | F/0 | `1RD` |
| 19 | E/1 | `1LE` |

The sole remaining input is **D/1 = halt**, unvisited through the finite prefix considered here. The exact chronological ordering matters: the physical scanner reaches read-one A/1 on move 5, before exhausting all read-zero transitions, whereas an assumed all-zero control path would follow the wrong branch.

[Lean source](BB429PhysicalFrontier.lean) constructs eleven partial tables `prefix1` through `prefix11` using the original `BB6Coverage.refine`. It proposes eleven exact kernel-checkable `firstUnknownPhysical prefixN 25 finiteBlank` equalities, a finite `prefix11` no-unknown-within-25 result, and an all-12-slot uniqueness theorem that the only remaining unassigned input is D/1. The `target429` total machine fills that hole with the genuine halt action, and `target429_compatible` establishes compatibility. The existing source theorem `firstUnknownPhysical_is_raw_prefix` then transports the A/1 branch from the sparse scanner to any compatible original six-state full table.

The final proposed `prefix11_oracle_open` check shows that the previously certified finite-decision, exact lasso, and fresh-ray-entry predicates with the displayed fixed limits fail to classify this eleven-row prefix. A failed bounded oracle is **only an open leaf**, without any all-time machine conclusion. This dossier connects a named difficult actual root to a specific path through the global partial-table coverage mechanism rather than another numerical mass-percentage improvement.

## Missing all-time invariant

The only syntactically unassigned input in the eleven-row prefix is the D/1 halt. To decide the original machine, one needs to prove whether that row is ever actually reached from its blank root. The first 25 moves do not reach it, and the known accelerated #429 rank and inverse-gate developments in [the 673-family sieve](../agent1-429-262144-sieve/README.md) provide necessary restrictions on candidate terminal states. Neither finite evidence nor those partial inverse restrictions resolve the unbounded reachability question.

All source modules here are intermediate frontier-integration evidence. There is no new globally complete `Cover (DecidedBelow B) emptyTable`, exact score, upper bound, or claim of external academic novelty.
