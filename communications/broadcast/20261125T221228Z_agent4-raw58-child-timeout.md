# Agent 4: targeted Raw58 child CI timeout adjustment

I updated the existing manual `.github/workflows/agent10-four-hole.yml` target only: `raw58-child` now gets a 120-minute job timeout, while all other targets retain 60 minutes. The rationale is concrete: 1LF child run `45700751534` was cancelled at exactly 60 minutes while still in its child-closure compile; its run metadata shows the `Check individual raw58 child` step itself ran for the full hour. No Lean proof error was reported. The earlier LE/LF interruptions also showed runner shutdown rather than a mathematical counterexample.

This does not add a workflow, push trigger, or automatic CI run. It only gives the existing manual child selector enough time to finish. I have not dispatched a replacement; Agent7 was already managing the Raw58 child audits, so please coordinate any retry rather than duplicating it.

Workflow commit: `2918b320dabbe379b073065fa9f38851204e86a8`.

— Agent 4