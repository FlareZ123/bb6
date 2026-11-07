# Machine C as an exact physical open path in the six-state global frontier

**Status, 7 November 2026.** Machine C itself remains undecided. The eleven-fixed-input authentic source cylinder has exactly 24 syntactically nonhalting alternative completions and one original unresolved machine. This is an intermediate global-enumeration case study; BB(6) remains open. The complete original raw table is
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` (suspect_46, holdout #39). The table agrees cell-by-cell with the recorded original Cryptids machine; the published reduction and its original-root counter model are [documented separately](../../resources/2026-11-02-deepmind-cryptids-machine-c.md).

## Current classification: one true holdout among 25 completions

The strongest original-source integrated theorem,
[`machineC_cylinder_raw_halts_iff_counter`](CryptidsPhysicalC.lean),
applies to **every full machine** `m` compatible with the actual
eleven-row physical Machine C prefix:

```lean
(∃ n, run m n blank = none) ↔
  (m machineCSourceHaltSlot = none ∧ BB6.CReachBridge.RunHalts)
```

Thus all possible halting within this 25-machine cylinder is **exactly**
equivalent to the single original Machine C three-counter stop question,
provided the free F/0 input is assigned its original HALT outcome.
It is source-verified in one Lean4.35.0-rc4 kernel check against pinned,
unchanged Google DeepMind Cryptids revision
`ced8f9f44f67a167d5ecc03e687b048c67926371`:
[manual CI **42338146301**](https://github.com/FlareZ123/bb6/actions/runs/42338146301).
The proof checks all 12 literal raw rows, transports physical halting
through the [generic Cryptids adapter](../agent4-coverage-smoke/CryptidsHaltIff.lean)
and published original-root source acceleration, and uses the existing
source-proved single-halt freedom lemmas. Its exact theorem's axiom audit
is `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.
The source counter stopping predicate `BB6.CReachBridge.RunHalts`
remains unclassified; the theorem supplies a genuinely unbounded,
source-checked reduction, with no new BB(6) upper or lower bound.

**Source verification, 7 November 2026.** The original all-time primitive-step
question is whether the genuine blank run ever *consults* the sole halting
table input **F/0**. The source-level theorem
`machineC_halts_iff_reads_F0` in
[`MachineCF0Root.lean`](MachineCF0Root.lean) establishes the biconditional

```
(∃ n, run machineC n blank = none) ↔
  ∃ n d, run machineC n blank = some d ∧
    readSlot d = machineCHaltSlot
```

The stronger theorem
`machineC_entire_cylinder_nonhalt_iff_F0_avoided` says that **all 25**
completions agreeing on the other eleven table entries are nonhalting
exactly when the original run avoids F/0 forever. It is a mathematical
equivalence with an unresolved right-hand premise. For a *hypothetical first*
F/0 consultation, `machineC_first_F0_common_prefix` and
`machineC_first_F0_halt_completion` transport the actual primitive-step
prefix and its halting score to every corresponding completion.

These all-time statements compiled against the unchanged original
six-state full-tape coverage semantics in
[manual Lean CI **42336664117**](https://github.com/FlareZ123/bb6/actions/runs/42336664117),
Lean 4.36.0-rc2. Every printed theorem depends only on `[propext]`,
with no `sorryAx`.

The independent [`MachineCOneSlotAudit.lean`](MachineCOneSlotAudit.lean)
uses the original `TotalHaltAudit.total_never` theorem to separate the
eleven-fixed-row cylinder at its *sole free input F/0*. Every one of the
**24 ordinary F/0 outcomes** gives a completely specified machine with
no halting transition at *any* input, so it cannot halt from any start.
The single F/0 HALT outcome is precisely the original undecided historical
Machine C. `machineCOneSlotAudit_mass` proves the exact frontier report
`(24, 1)`, and `machineCOneSlotAudit_exhaustive` proves source-sound
coverage of every compatible full machine. All final statements passed
[manual Lean CI **42337612928**](https://github.com/FlareZ123/bb6/actions/runs/42337612928)
using only standard logical axioms, without `sorryAx`.

The earlier original-global-tree result `machineC_depth_eleven_open`
reflected failure of its **finite lasso/macro oracle** to certify any
of those 25 continuations. The new 24/1 split uses the separate direct
syntactic no-halt-transition theorem and does not contradict that finite
oracle result. **No new historic machine is classified:** the 24 easy
completions already have no halting instruction, and the one meaningful
holdout is unchanged. No numerical BB(6) bound follows.

The appropriate remaining work is a source-verified all-time exclusion of
F/0 for the original Machine C run, or an actual primitive-step halting
witness. The associated three-counter stopping and original raw-machine
semantic reductions provide potential proof targets. This entire
dossier remains intermediate, under `im-results/`.


## Supporting evidence: primitive blank-run prefix

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

## Earlier finite-oracle outcome in the global classifier

[`MachineCFrontier.lean`](MachineCFrontier.lean) targets Agent32's exact depth-four combined `lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4`. It checks the first four source-read slots (A/0, B/0, C/1, C/0), checks each corresponding source-sound `lassoDecisionOracle` outcome (false, meaning no *available sufficient certificate*), and then constructs an explicit proof of `FrontierAudit.open machineC` along the four genuine children. This identifies an unresolved global leaf, rather than merely a synthetic tree path. Its four-row leaf has exact weight `25^8` complete tables. It includes Machine C but most of those completions have other transitions.

**Formal status for this second module:** [manual original-dependency Lean CI run 42323041110](https://github.com/FlareZ123/bb6/actions/runs/42323041110) **succeeded** at commit `3955340798f18a8c6f383caa6b2f994768c8877e`, compiling the unmodified source dependencies and both `MachineCFrontier.lean` and `MachineCElevenFrontier.lean`. Its successful source-proof job includes the constructive all-four-split theorem `machineC_depth_four_open`; the file retains `#print axioms` commands for the essential statements. An earlier build [42321777224](https://github.com/FlareZ123/bb6/actions/runs/42321777224) failed to elaborate a `by decide` for the dependent `FrontierAudit.open` predicate and was superseded by the constructive proof. This verified open-leaf theorem expresses only absence of a certificate from the chosen finite oracles, never a machine halting outcome.

These four specific global-tree children show why the existing physical lasso/macro classifier does not close this genuine holdout at its published depth-four limits. In particular, a false oracle outcome establishes only failure of *its finite sufficient tests*; it is not evidence of future halting or nonhalting.

## Remaining mathematical barrier: unbounded F/0 avoidance

All eleven nonhalting source rows were seen in a very short actual execution, so further syntactic enumeration of free transition rows on this particular authentic root terminates immediately at F/0. The open all-time question is whether F/0 is ever physically consulted. The already certified Machine C source acceleration reduces this to two infinite Diophantine stopping-parameter families and an exact fixed-target predecessor evaluator; the latest root-connected [joint criterion](../agent19-c-odd-dyadic/JointCriterionIntegration.md) still has unbounded low/high parameters. Neither this finite prefix nor the global finite lasso/macro screen decides those quantifiers.

The appropriate extension is a true source-closed invariant through all exceptional counter returns, or a genuine halting witness. A longer finite trace, or closing only easy raw-table cylinders, does not replace that proof. This dossier stays in `im-results/` unless genuinely new all-time mathematics is established.

## Exact raw-mass box for fixed-target root experiments

CResidualMassBounds.lean derives exact weighted-mass formulas for the two stopping-target families and proves a finite parameter box for the current raw-mass cutoff 2000:

- Low target: M_low(m) = 2^(2m+4) - (6m+7). If M_low(m) <= 2000, then m <= 3.
- High target: M_high(j,m) = 2^(2m+3)(j+3) - (6m+7). If M_high(j,m) <= 2000, then m <= 3 and j <= 250.

The proofs establish M_low(m) >= 4065 and M_high(j,m) >= 6113 for every m >= 4. Thus the rectangle 0 <= m <= 3, 0 <= j <= 250 contains every high target under the raw-mass cap, and 0 <= m <= 3 contains every low target under that cap. The sharper theorem high_raw_mass_box_exact gives the exact per-row bounds: m=0 has j<=247 (248 values), m=1 has j<=59 (60 values), m=2 has j<=12 (13 values), and m=3 has j=0 (1 value). Together with the four low targets, this is exactly 326 unfiltered target points.

This is a **search-domain theorem**, not a nonhalting theorem. The existing CResidualProbe.lean still samples only the first two allowed high j-values per m and imposes a root-fuel cap of 256. It therefore does not yet exhaust the full raw-mass-2000 domain. The new bound makes an exhaustive finite scan possible once every allowed pair in the box is evaluated and every root-fuel skip is eliminated or explicitly retained.

CResidualMassBounds.lean compiled locally with Lean 4.36.0-rc2. Its six printed theorem audits use only [propext, Quot.sound]; no sorryAx is present.

## Finite raw-mass-2000 reachability exclusion

[CResidualMass2000.lean](CResidualMass2000.lean) turns the parameter box above into an exact finite root-exclusion certificate. It evaluates the source-faithful forward `massStop` test on every unfiltered target in the box: 4 low targets and 322 high targets, split into rows of 248, 60, 13, and 1. The row propositions are closed Lean computations proved by `decide`. The file then uses `SectionFuelOriginal.massStopHalfFull_iff` to prove that none of these targets belongs to the blank-root section orbit.

The resulting theorems `low_reach_implies_mass_gt_2000` and `high_reach_implies_mass_gt_2000` state that **every reachable target in either complete low/high stopping family has weighted mass strictly greater than 2000**. No C70, C23, phase, or other parameter filters are assumed, so the finite exclusion covers a superset of the currently surviving candidates. This is a finite lower bound on the stopping-target mass; it does not establish that the machine is nonhalting, and it does not determine BB(6).

The finite row computations were independently compiled locally with Lean 4.36.0-rc2 using a line-for-line copy of the executable `bounceFuel`, `secNextFuel`, and `massStop` definitions from SectionFuelOriginal. The repository module imports the original SectionFuelOriginal source and will be checked by the all-phase CI workflow. The local row theorems have no axioms; the reachability corollaries rely on the source `massStopHalfFull_iff` bridge and the arithmetic bounds in CResidualMassBounds. No `sorryAx` was used in the local certificate.
