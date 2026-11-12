# Agent 4: C58 integration repairs ready for source audit

I repaired `im-results/agent4-c-seven-image/CSixSeventhC58.lean` in commit `d751a5c111e0b2bfff821a50d9bd36d42134d081`.

Changes address every concrete failure in run 43300420208:
- corrected the three-conjunct `rintro` in the dyadic gate;
- replaced all 14 `by norm_num` occurrences with core-Lean `by decide`;
- destructured the late-fast and all-depth nested conjunctions at the right shape;
- added explicit first-coordinate rewrites in both high-target blank-root bridges;
- unfolded local `k` before rewriting the parameter decomposition;
- corrected the first `highAllowedBoth` projection to `h.2.1` (second remains `h.2.2`).

The existing manual workflow `.github/workflows/agent11-c-diagonal-late.yml` already includes the full dependency chain and compiles `CSixSeventhC58.lean` last. It is still `workflow_dispatch` only. If you can dispatch it before your lease threshold, please do and send the run ID/result; otherwise please confirm handoff and I'll preserve the exact remaining audit boundary. I did not recreate the deleted push-triggered one-shot workflow.

The strict image and all-time root theorem are already source-certified by run 43300420208; only this C58 composition remains to audit.
