# Machine C as an exact physical open path in the six-state global frontier

**Status, 7 November 2026.** This is a source-connected, proof-carrying *intermediate* global-enumeration case study. The historical Machine C holdout, and therefore BB(6), remain unresolved. The complete original raw table is
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` (suspect_46, holdout #39). The table agrees cell-by-cell with the recorded original Cryptids machine; the published reduction and its original-root counter model are [documented separately](../../resources/2026-11-02-deepmind-cryptids-machine-c.md).

## Proven physical prefix

[`MachineCPath.lean`](MachineCPath.lean) defines the canonical twelve-input `BB6Coverage.Machine` table, using unmodified original `Frontier`, `RayFinite`, and Agent32 physical-trace definitions. The new theorem `machineCPrefix_compatible` proves that the first `n` distinct visited source inputs, fixed at the literal Machine C outcomes, are compatible with Machine C for every `n`.

The actual blank-tape physical trace first consults the following eleven *different* inputs:

| First consultation (successful moves) | State/symbol |
|---:|---|
| 0 | A/0 |
| 1 | B/0 |
| 2 | C/1 |
| 4 | C/0 |
| 6 | B/1 |
| 7 | D/1 |
| 8 | E/0 |
| 9 | F/1 |
| 13 | D/0 |
| 16 | A/1 |
| 22 | E/1 |

This is a physical-tape trace: a previously written one is read as one. The twelfth input, F/0, is the original halt row and is **not read during this certified prefix**. The exact `machineC_first_slots`, `machineC_discovery_times`, and `machineC_blank_prefix_no_other_input` statements are established by finite kernel reduction and the original `firstUnknownPhysical` / `finitePartialRun` semantics.

The `machineCPrefix_uniform_23` theorem uses the original-source `finitePartialRun_sound` bridge: **every** total machine extending these eleven assigned entries executes at least 23 successful primitive steps. There are exactly `25` such total machines, because F/0 is the sole free input, with `machineCPrefix_mass` proving this cylinder mass. The raw trace's first 23 moves are uniform across the entire cylinder. This gives no all-time nonhalting certificate and no new numerical lower bound on BB(6).

The first original-source manual Lean 4.36.0-rc2 CI [run 42321539218](https://github.com/FlareZ123/bb6/actions/runs/42321539218) **succeeded**, compiling all original dependencies with standard axioms only. This certifies the statements above at exact source revision `7e857caf337cfe7ca0532b8e96ac6ef21b3dbe4c`.

## Genuine path through the combined global classifier

[`MachineCFrontier.lean`](MachineCFrontier.lean) targets Agent32's exact depth-four combined `lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4`. It checks the first four source-read slots (A/0, B/0, C/1, C/0), checks each corresponding source-sound `lassoDecisionOracle` outcome (false, meaning no *available sufficient certificate*), and then constructs an explicit proof of `FrontierAudit.open machineC` along the four genuine children. This identifies an unresolved global leaf, rather than merely a synthetic tree path. Its four-row leaf has exact weight `25^8` complete tables. It includes Machine C but most of those completions have other transitions.

**Formal status for this second module:** the first full-source CI attempt [42321777224](https://github.com/FlareZ123/bb6/actions/runs/42321777224) checked the concrete slot/oracle facts and mass, but rejected the attempted `by decide` for `FrontierAudit.open` (dependent type has no computable `Decidable` instance). The theorem was then rewritten as a four-step constructive proof; final original-source CI confirmation is **pending**. Do not treat this particular openness theorem as source-certified until the replacement build passes and is audited. This failure is a proof elaboration issue, not negative evidence about Machine C.

These four specific global-tree children show why the existing physical lasso/macro classifier does not close this genuine holdout at its published depth-four limits. In particular, a false oracle outcome establishes only failure of *its finite sufficient tests*; it is not evidence of future halting or nonhalting.

## Remaining mathematical barrier

All eleven nonhalting source rows were seen in a very short actual execution, so further syntactic enumeration of free transition rows on this particular authentic root terminates immediately at F/0. The open all-time question is whether F/0 is ever physically consulted. The already certified Machine C source acceleration reduces this to two infinite Diophantine stopping-parameter families and an exact fixed-target predecessor evaluator; the latest root-connected [joint criterion](../agent19-c-odd-dyadic/JointCriterionIntegration.md) still has unbounded low/high parameters. Neither this finite prefix nor the global finite lasso/macro screen decides those quantifiers.

The appropriate extension is a true source-closed invariant through all exceptional counter returns, or a genuine halting witness. A longer finite trace, or closing only easy raw-table cylinders, does not replace that proof. This dossier stays in `im-results/` unless genuinely new all-time mathematics is established.
