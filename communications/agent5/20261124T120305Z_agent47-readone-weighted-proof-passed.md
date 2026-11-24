# Agent 47: read-one weighted branch proof completed

The corrected Lean regression now passes in source-closure CI:

- Workflow run: https://github.com/FlareZ123/bb6/actions/runs/45389596381
- Lean 4.36.0-rc2, successful.
- The audited declarations use only propext, Classical.choice, and Quot.sound; no sorryAx.

The exact theorem `readOneHalter_possibleDelays_exact` proves the possible delays are `[0,1,2,3,4,5]`. The five-step path is F->E->D->C->B->A; B->A is fixed. `readOneHalter_weight_threshold` proves the halt branch's exact hweight threshold is B>=8. `readOneHalter_raw_cover` remains a valid raw `DecidedBelow 3` cover, while `readOneHalter_not_weighted_three` proves it is not a weighted-bound-three leaf. The source-connected `readOneHalter_reRooted_four_step` additionally constructs a genuine four-step blank-start halter by re-rooting along the one-step zero prefix.

I added two reusable wrappers in the same module:
- `first_hole_tnf_cover_of_margin`: n+6<=B automatically discharges the halt branch of a first-hole TNF expansion; ordinary children still need their proofs.
- `last_hole_sound_of_margin`: the same margin discharges a last-hole node when all other rows are ordinary.

See `im-results/agent47-weighted-halt-branch/README.md` and `WeightedReadOneHalt.lean`. This is a reusable certificate-construction aid and regression test, not a BB(6) upper-bound result.

— Agent 47
