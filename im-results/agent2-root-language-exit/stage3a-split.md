# Eighteenth D-root reentry: split validation protocol

The seventeenth authentic blank-root reentry is source-certified by stage-2b17i
run [43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437),
which preserves artifact d-root-stage2b17i at source snapshot
b3cc897d85ff6c69ca29a24be2aa3bf6931e13f7. The follow-on stage-2b17j run
[43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093)
compiles the E7 escape and preserves d-root-stage2b17j at source snapshot
20509b53af45edce5b8a145e8714245d3d225cdd. Commit 20509 is a one-commit child
of b3cc and changes only ExceptionalE7ThirdReturnEscape.lean (+5/−2);
BlankSeventeenthRejoin.lean imports ExceptionalE7ThirdReturn.lean, not that
changed file. The stage-2b17i predecessor .olean closure is therefore
source-content compatible with the 20509 snapshot used by stage-2b17j and
by the split eighteenth workflow.

The next submitted eighteenth segment was attempted in run
[43844908990](https://github.com/FlareZ123/bb6/actions/runs/43844908990).
That run was cancelled while its compile step was still in progress and produced
no artifact or Lean diagnostic. It is therefore an interrupted validation, not
a Lean counterexample or a verified eighteenth reentry.

To avoid rerunning the same monolithic compilation, the original 18th proof is
split at its actual logical boundaries:

1. EighteenthArithmetic.lean: certify the 2,902-step DRegular segment and
   its terminal residue, using the already checked 64-step evaluator.
2. EighteenthRootPrefix.lean: lift that exact segment from the certified
   seventeenth blank-root reentry to the authentic eighteenth exception.
3. BlankEighteenthRejoin.lean: apply the original-source E/B packet return
   and reach L(64*t18+23,1,5).

The manual workflow
[agent2-d-root-stage3a-split.yml](../../.github/workflows/agent2-d-root-stage3a-split.yml)
uses two explicit snapshots: the mathematical base remains pinned to
20509b53af45edce5b8a145e8714245d3d225cdd, matching the predecessor
artifact; extension_ref pins the repository commit from which the workflow copies
only the three split proof modules. The workflow records both commits in its artifact markers and checks
that the extension commit remains identical across all three runs.

Run order:

| Stage | Predecessor artifact | Output artifact | Required source theorem |
|---|---|---|---|
| 1 | d-root-stage2b17j (run 43761344093) | d-root-stage3a1 | 2,902-step arithmetic certificate |
| 2 | d-root-stage3a1 | d-root-stage3a2 | authentic eighteenth exception |
| 3 | d-root-stage3a2 | d-root-stage3a | E/B packet reentry |

After stage 3 succeeds, resume the existing
[agent25-eleventh-root.yml](../../.github/workflows/agent25-eleventh-root.yml)
workflow at stage 3b, with predecessor artifact d-root-stage3a, its
successful run ID, and the same base source_ref.

The first split stage-1 run [44076940240](https://github.com/FlareZ123/bb6/actions/runs/44076940240) exposed a stale namespace reference: the submitted file used Agent2SeventeenthRoot.u17, but the predecessor defines the parameter as Agent2SeventeenthArithmetic.t17 / 3. The arithmetic module now defines this local alias explicitly; the failed run produced no artifact and is not evidence against the mathematical trajectory. The corrected rerun is queued as [44078315654](https://github.com/FlareZ123/bb6/actions/runs/44078315654), with the extension snapshot pinned at 2dcc75abcf2e0ca06c877336fad1d2d8d07e0abd.\n\nUntil stage 3 succeeds, the eighteenth reentry remains a submitted candidate.
Do not promote the D-root prefix beyond the sixteenth/seventeenth evidence
already supported by completed source CI, and do not infer an all-time
nonhalting result or any BB(6) value from this finite chain.
