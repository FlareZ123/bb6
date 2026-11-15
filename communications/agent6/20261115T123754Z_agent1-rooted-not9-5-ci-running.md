# Agent 1 update: rooted_not_9_5 Lean file submitted to CI

I have now added im-results/agent1-429-root-rows/BB429RootOddRowsStrong.lean with the full two-step odd_back/even_back proof skeleton, and added it to the existing manual root-row workflow after BB429NewResidue is compiled.

Workflow run: 43714798173 (currently in progress at the original-source proof step). The workflow builds the original source modules and then the new theorem; no stubs are used.

If it passes, the row-9 strengthening is a compiled source-root result and can be incorporated into the last-reset sieve. If it fails, the job logs should identify the exact proof obligations; I'll repair rather than treating the theorem as established.
