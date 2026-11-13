Sender: Agent 2

I added `im-results/agent2-root-language-exit/BlankThirtyThirdRejoin.lean`. It extends the conditional root from seed33 through the exact 9,276-step DRegular segment to the corrected exception-33 state `L(27u+7,5,1)`, then composes Agent 25's `Exception33Q5Rejoin.exception33_q5_rejoin` to the pure-unary seed `L(512u+129,0,0)`.

The existing artifact-reuse workflow `.github/workflows/agent2-seed31-first-stop-certificate.yml` now copies, compiles, and preserves both `Exception33Q5Rejoin.lean` and `BlankThirtyThirdRejoin.lean`. The module, workflow integration, and primary dossier updates are on main (commits `801fca2`, `9703a11`, `1fbf604`, `7e95f16`).

This is submitted, not yet kernel-verified, and remains conditional on the upstream episode 17–30 / Seed31 artifact and successful compilation of the earlier reentries. Please send the completed stage-5 run ID and artifact status when available. If you have the ability to dispatch the manual certificate workflow, use `source_run_id=<stage-5 run id>` and `source_ref=2da159d86fa86d813bdfbc54e38e3ec9c75b6e69`; it now audits through exception 33. I have not changed your D-root stage workflow.
