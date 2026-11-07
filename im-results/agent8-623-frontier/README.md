# Authentic #623 root in the proof-carrying six-state frontier

**Research status (7 November 2026):** intermediate source-integration and authenticated finite physical trace. The original six-state machine's halting outcome is **unknown**. No BB(6) value, maximum bound, new difficult-root decision, or publishable machine result is asserted.

## Concrete target and theorem

The rooted machine is `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, DeepMind Cryptids #623, with start state A, entirely blank tape, and unique absent (halting) input F/0. The corresponding pinned [Cryptids upstream module](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean) gives an independent halting-equivalent acceleration from section state `D(0,7)`. An acceleration theorem is not a halting verdict.

[`Machine623Path.lean`](Machine623Path.lean) represents all twelve original RLE transition inputs in the repository's canonical `BB6Coverage.Machine` model and reconstructs the literal **physical two-way tape execution**. The eleven distinct first-consulted state/read-symbol inputs, in order, are:

| Primitive move index | Input |
| ---: | :--- |
| 0 | A/0 |
| 1 | B/0 |
| 2 | C/0 |
| 3 | D/0 |
| 6 | D/1 |
| 9 | C/1 |
| 11 | B/1 |
| 13 | A/1 |
| 14 | E/1 |
| 52 | E/0 |
| 53 | F/1 |

The final F/0 row is genuinely unused through the first 96 primitive moves. The eleven-row partial table `machine623Prefix 11` has one free slot and represents exactly `25` full-table completions. `machine623_uniform_54` proves, **for every full machine compatible with these eleven rows**, successful blank execution through 54 primitive ordinary moves. This is an exact structural theorem about a physical prefix and does not extrapolate to the infinite future.

[Independent literal RLE evaluator](verify_route.py) checks the first 96 primitive moves and the exact discovery-time list without using the accelerated arithmetic. Its observations are finite corroboration, not the proof.

## Explicit global open-leaf trace

[`Machine623Frontier.lean`](Machine623Frontier.lean) tracks the first four genuinely consulted sparse slots A/0, B/0, C/0, D/0 through the original proof-carrying `lassoPhysicalTraceAudit` decision tree of [Agent32](../agent32-zero-prefix-global/README.md). The finite-halt, ray, lasso and finite-entry-macro oracles return `false` at each of the first five prefix states with parameters `bound=6, rayLimit=6, lassoLimit=12, entryLimit=2, macroLimit=4`. At split depth four, the branch should remain explicitly open, with its prefix-cylinder `25^8` possible full transition tables. The oracle's false result is **lack of a certificate**, not evidence of halting or nonhalting.

## Source provenance and proof boundaries

- The locally defined `Machine623Path.lean` finite-prefix and cardinality theorems were compiled against unchanged Agent8/32 canonical-table modules in [manual CI run 42322273466](https://github.com/FlareZ123/bb6/actions/runs/42322273466). The same run **failed on the later open-leaf theorem**, due to a noncomputable `Prop` decidability proof. The finite-prefix theorem's successful axiom audit was `[propext, Classical.choice, Quot.sound]`; the mass theorem has no axioms. Subsequent attempts should be checked separately.
- [`Machine623Source.lean`](Machine623Source.lean) connects the literal table to the unmodified pinned Cryptids machine through the already source-proven [tape adapter](../agent4-coverage-smoke/CryptidsTapeAdapter.lean). This imported proof must pass the separate [manual upstream source workflow](../../.github/workflows/agent8-623-source.yml) before being described as source-verified.
- The [manual canonical frontier workflow](../../.github/workflows/agent8-623-frontier.yml) rebuilds every shared dependency, including the actual nonhalting-or-halt leaf oracle, before the #623 tests. It has no per-commit trigger.
- Earlier [Cryptids #623 arithmetic results](../agent8-623-inverse/README.md) and [Agent49 parity/gate analysis](../agent49-parity623/README.md) give source-level necessary restrictions, including a logarithmically narrow candidate halting corridor. They have not supplied a genuine blank-root exclusion or witness.

## Remaining quantified question

The exact missing result is an all-time theorem for the full source machine rooted at blank A: either its raw execution never consults F/0, or it reaches F/0 after a known number of successful primitive moves. Only such a result would turn the existing full-table #623 open leaf into an authentic halt/nonhalt certificate. The existing source halting equivalence allows the same question to be phrased as whether the accelerated `D(0,7)` orbit ever enters a failure state; source-derived parity, mass growth and inverse grammar do not yet determine that existential.

A useful next experiment is to extract the precise first surviving stopping-gate family admitted by Agent49's full source bounds, then establish an all-time inverse or history-sensitive exclusion tied to `D(0,7)`. The partial source branches here merely expose exactly where that missing theorem must be inserted. Avoid interpreting the `25^8` open mass as eight missing transition decisions for the single rooted holdout.
