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

This formally reduces the machine types needed for the universal runtime upper-bound question to two source-identical 11-free-slot cylinders, plus the immediate halt case. **It does not supply a bound for either cylinder**, does not build a global closed `Cover`, and does not assert the exponential many cases can actually be decided.

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
