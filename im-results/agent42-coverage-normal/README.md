# Root-preserving first-instruction normalization for six-state blank-tape machines

**Status:** verified intermediate proof infrastructure; **BB(6) remains open**. From Agent42's R005 coverage audit on 2026-11-03. The normal-form principle is standard folklore; we make no claim of mathematical priority or novelty.

## Exact theorems

Two Lean 4.36.0-rc2 modules use the unmodified, source-certified `BB6Coverage` semantics (`Fin 6 × Bool` input slots, full `Int → Bool` tape, blank state A, each of 25 outcomes assigned to all 12 input slots). `HaltsAfter m n` means `n` successful ordinary instructions followed by the halting query; the Busy Beaver score is `n+1`. No partial-prefix simulation is used to justify the equivalence.

1. [FirstStep.lean](FirstStep.lean):
   - `swapToOne` is a six-state permutation that fixes blank-start A whenever the initial target `q ≠ A`, and sends `q` to B.
   - `normal_first_other`: state permutation plus optional left/right reflection maps each first instruction `wDq` with `q ≠ A` to `wRB` without changing **any** `HaltsAfter m n` truth value.
   - `normal_first_self`: reflection or identity maps first moves returning to A to `wRA`.
   - `normalize_first`: every complete six-state table is exactly-runtime equivalent to one whose first A/0 action is one of `halt,0RA,1RA,0RB,1RB`.
   - `upper_from_five_first_actions` transfers any runtime bound on the five canonical classes to *all* standard six-state complete tables.

2. [TwoFirst.lean](TwoFirst.lean):
   - Source-imports the existing `blankDrift_never` for first instruction `0RA` and the existing `writeOneRight_never` for first instruction `1RA`, both all-time blank nonhalting proofs.
   - `positive_halter_two_first`: any `HaltsAfter m n` with `n>0` has a source-semantics equivalent six-state table with first A/0 action **either `0RB` or `1RB`**, retaining every halting time. The immediate halt case has only score one; both A-self-loop cases never halt.
   - `upper_from_two_first_actions B`: if `B ≥ 1` and every halter whose first action is `0RB` or `1RB` has score at most `B`, then every six-state halter has score at most `B`.

This formally reduces the machine types needed for the universal runtime upper-bound question to two source-identical 11-free-slot cylinders, plus the immediate halt case.

3. [CrossFirstUpper.lean](CrossFirstUpper.lean):
   - `raw_upper_iff_two_first` combines the two-action normal form with the pre-existing original-source Agent13/Agent8 whole-machine bridge. For any `B ≥ 1`, a universal bound over **all raw 28-action six-state machines** is equivalent to a bound over all original 25-action machines whose first action is `0RB` or `1RB`.
   - `exact_from_two_first_and_raw_witness` is a conditional source-level `BB6.Coverage.ExactBB6 B` theorem requiring a raw halting witness attaining B and the two-action universal bound.
4. [TwoCylinder.lean](TwoCylinder.lean):
   - Defines two genuinely sparse first-slot partial tables, `firstZeroCylinder` and `firstOneCylinder`, with the other 11 slots unassigned.
   - `raw_upper_from_two_cylinder_covers` consumes actual `Cover (DecidedBelow B)` proof objects for precisely those two partial tables and proves the universal full raw 28-action upper bound.
   - `exact_from_two_cylinder_covers` combines **only these two source-authentic sparse coverage certificates** with a raw champion witness to derive `ExactBB6 B`. This is a verified *conditional proof interface*; the two certificates and champion witness are missing.

**Follow-up source CI:** [job 125650419159 in run 41554636763](https://github.com/FlareZ123/bb6/actions/runs/41554636763/job/125650419159), Lean 4.36.0-rc2, full unmodified original Agent8/Agent13 `CrossCoverage.lean` and `CrossUpper.lean` imports, compiled `CrossFirstUpper.lean` and `TwoCylinder.lean`; both direct `ExactBB6 B` theorems use only `[propext, Classical.choice, Quot.sound]`. No `sorryAx`. The overall workflow's other unrelated `formal-check` job still fails, so cite the isolated successful job. This is an actual first-branch *completeness contract* and a direct consumer of sparse `Cover`, while stopping short of closing either nontrivial root cylinder.
 **It does not supply a bound for either cylinder**, does not build a global closed `Cover`, and does not assert the exponential many cases can actually be decided.

## Verification and reproducibility

The **unmodified source modules** `Frontier.lean`, `Symmetry.lean`, `Prune.lean`, `WriteOneDrift.lean`, followed by both new files, were independently compiled by [successful standalone CI job 125647657349 in run 41553812046](https://github.com/FlareZ123/bb6/actions/runs/41553812046/job/125647657349), for source revision `13bc1ec833fac87347febad4d1d0c05a6a7a8a86`. All four named concluding theorems report exactly the ordinary Lean axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`:

- `BB6Coverage.normal_first_other`
- `BB6Coverage.normalize_first`
- `BB6Coverage.positive_halter_two_first`
- `BB6Coverage.upper_from_two_first_actions`

The manual-only existing workflow `.github/workflows/agent8-coverage-contract.yml` contains a separate `agent42-first-action-normal-form` job and has **no per-commit trigger**. The separate pre-existing `formal-check` job failed later at an unrelated `MarkerOracle.lean` proof (Agent6 informed), so the *overall workflow result* is failure. The **independently successful new proof job** above is the actual evidence; do not misreport the whole workflow as passing. Earlier attempts at the exact `blankAt A = blank` conversion failed, and were corrected before the successful source check.

## Relevance, prior art, and remaining obligations

This is a reusable **root-correctness reduction** of a universal theorem, not a novel decision about any historic holdout. Its proof imports the preexisting original-source state-renaming and tape-reflection equivalences. It should remain in `im-results/`, not the academically publishable `results/`.

A complete BB(6) argument still requires (i) an attained raw-table champion score with exact primitive-step semantics, and (ii) a source-certified universal bound for all blank A/0-`0RB` and A/0-`1RB` machines or another exhaustive complete certificate. Existing imported DeepMind A6/F287 nonhalting certificates classify a known root only and preserve essentially the whole unresolved universe. The previous [R005 frontier audit](../agent4-coverage-smoke/FRONTIER-AUDIT.md), [Agent13 contract](../agent13-coverage/README.md), and [Agent8 source contract](../agent8-coverage-contract/README.md) explain why conditional source certification, historical holdout lists, and disjoint mass conservation cannot by themselves establish a global bound.

**Next useful research:** turn `TwoFirst` into a directly consumable two-cylinder complete-frontier theorem (rather than only the score upper bound) if a concrete enumerator needs it; or work on a genuine blank-root nonhalting decision with an identified remaining halting instruction and integrate that proof as an authentic sparse leaf.


## Source-checked exact 0RB blank-prefix trim (standard TNF-1RB mechanism)

[ZeroPrefix.lean](ZeroPrefix.lean) provides an additional exact score interface:
- `zeroRB_first_config`: on a true original blank A-root whose first instruction is `0RB`, the configuration after exactly one move is a physical translation by +1 of the untouched blank B-root configuration.
- `zeroRB_shifted_suffix`: for **every** finite step count `k` (including runs that already halted), the original run at `k+1` equals the spatially shifted, B-blank-root run at `k`.
- `zeroRB_trim_haltsAt`: `HaltsAfter m (k+1) ↔ HaltsAfterAt m B k`.
- `zeroRB_trim_permuted`: re-root B back to conventional A by the explicit A↔B state permutation, yielding `HaltsAfter m (k+1) ↔ HaltsAfter (renameTable swapAB m) k` for all `k`.

This is the first exact primitive-step link needed when studying a `0RB` prefix using TNF-1RB representatives, with the exact one-step loss tracked. It is a known observation, explained in the [BusyBeaverWiki Tree Normal Form, TNF-1RB section](https://wiki.bbchallenge.org/wiki/TNF#TNF-1RB). Our contribution is a local kernel-checked version in the shared semantics; there is **no claim of mathematical novelty** or completeness of an iterative 0RB-prefix elimination. In particular, a universal **exact steps** upper bound cannot simply discard `0RB` roots without accounting for these omitted prefix steps.

Source proof verification: [run 41556778926, isolated job 125657500277](https://github.com/FlareZ123/bb6/actions/runs/41556778926/job/125657500277) **SUCCESS**, Lean 4.36.0-rc2, original `RootShift.lean` and `Symmetry.lean`; all four theorem axiom audits only `[propext, Classical.choice, Quot.sound]` (some use fewer), **no** `sorryAx`. The unrelated existing `formal-check` job continued to fail from Agent6's `MarkerOracle`, so only the new isolated job's result establishes source proof success.


## Exact 0RB cylinder census of pure zero-writing recurrent control paths

[zero_cycle_census.cjs](zero_cycle_census.cjs) independently exhausts **all `25^5=9,765,625`** assignments of the five unfixed *read-zero* transitions B/0 through F/0, with A/0 fixed to 0RB. Every read-one transition is arbitrary because any recognized zero-writing recurrent path keeps the tape pristine forever. The checker independently compares a primitive transition-path simulation with a symbolic first-repeat count, and fails if either total differs.

For a first repeated state after exactly `k` distinct visited states, `2≤k≤6`, the number of assignments is

```text
C_k = (product_{j=2}^{k-1} 2*(6-j)) * (2*k) * 25^(6-k)
k=2: 1,562,500
k=3:   750,000
k=4:   240,000
k=5:    48,000
k=6:     4,608
sum: 2,605,108 / 9,765,625 = 26.67630592%.
```

Explanation: A's fixed transition visits B, yielding two visited states; each newly encountered state's read-zero instruction has exactly two directions and `6-j` unvisited successor choices if it expands the blank-only control path at `j` visited states, or two directions and `j` successor choices if it closes a cycle. Once a successor revisits a state, the same read-zero zero-writing instructions run forever on a pristine tape regardless of head movement. All remaining unvisited read-zero transitions and all six read-one transitions are free. Thus the exact number of classified *complete 25-action six-state tables* in the 0RB cylinder is

```text
2,605,108 * 25^6 = 636,012,695,312,500
```

This is an **exact finite computational/case-analysis census, not a new universally certified Busy Beaver upper bound or a new original-root decision**. Its all-time nonhalting semantic certificate is already provided by the existing `BB6Coverage.zeroMaskCheck_sound` / `zeroMaskOracle_sound` source theorems in [Agent8's ZeroMaskOracle.lean](../agent8-coverage-contract/ZeroMaskOracle.lean); this census does **not** itself construct an individual Lean `Cover` for all counted cases, and does **not** count additional nonhalting mechanisms such as positive-writer gliders. Under the fixed 0RB prefix, the direct state path criterion is equivalent to the presence of an initial-state-containing closed zero-writer mask, since only six states can be visited before repetition. The census quantifies this single existing decidable mechanism in the entire first-root cylinder and can guide traversal/branch ordering.

Verified [GitHub Actions run 41557492548, isolated job 125659828562](https://github.com/FlareZ123/bb6/actions/runs/41557492548/job/125659828562), successful Node.js exhaustive+formula check alongside the previous successful Lean source-level theorems. The overall workflow still had an independent older job failure.


## Source-certified linear-time zero-path mask witness

[PathMask.lean](PathMask.lean) is an optional faster **positive-certificate** path for the existing `zeroMaskOracle`. `collectZeroPath` follows the already assigned read-zero transition from A, recording visited control states (max 6). It stops with no certificate if a read-zero transition is unassigned, halts, or writes one. If it encounters a repeated state, `pathMaskCheck` submits its visited-state mask to the **original unchanged** `zeroMaskCheck`, which explicitly verifies each member's assigned zero-write closure.

`pathMaskCheck_sound` is an unconditional Lean proof that acceptance yields `Cover (DecidedBelow B) p` for **any six-state partial table and every bound B**. It reuses Agent8's already source-checked `zeroMaskCheck_sound` without asserting results from mere graph heuristics. [Source CI run 41557948889, isolated job 125661323179](https://github.com/FlareZ123/bb6/actions/runs/41557948889/job/125661323179) and [run 41558287553, job 125662448584](https://github.com/FlareZ123/bb6/actions/runs/41558287553/job/125662448584) succeeded with only `[propext, Classical.choice, Quot.sound]`.

The detector is `O(6)` read-zero path queries plus one independent 6-state mask check when successful, rather than scanning 64 candidate masks. It is **proven sound, not formally proven complete relative to the 64-mask oracle**; all negative responses are inconclusive. An independent [fixed-seed simulation crosscheck](path_mask_crosscheck.cjs) covered 250,000 complete 0RB read-zero rows plus 250,000 arbitrarily partially assigned rows with zero discrepancies against a direct 64-mask enumeration, [CI job 125662448584](https://github.com/FlareZ123/bb6/actions/runs/41558287553/job/125662448584). This sampled agreement supports the intended equivalence, but must not be represented as a Lean theorem or as classification of other nonhalting mechanisms. The method is presently opt-in; it has not been silently substituted for the existing shared oracle. Further source work could prove equivalence and replace the 64-way check without sacrificing coverage.
