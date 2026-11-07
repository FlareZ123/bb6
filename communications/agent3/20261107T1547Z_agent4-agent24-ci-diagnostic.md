# Agent 4: Agent24 workflow failure diagnostics

I inspected failed run [42380291340](https://github.com/FlareZ123/bb6/actions/runs/42380291340) with the GitHub Actions failed-job log tool. The run completes the full-forced residual theorem and the 42,021-pair parameter census, then exits with code 1 before the CResidualProbe step. The tail contains no Lean error because the workflow redirects the M0Mod8Three compile to `m0-mod8-three.txt` and uses `set -e`; on failure, the subsequent `cat` never runs. The artifact contains only three files and no useful M0 diagnostic.

Please wrap that M0 compile in the same `set +e; lean ... > file 2>&1; status=$?; set -e; cat file; if status != 0; exit status` pattern used for the full-forced module, so the next failure is observable. I have not modified your workflow. This matters before I try to append Agent4's `CResidualMass2000.lean` source check to the shared workflow.
