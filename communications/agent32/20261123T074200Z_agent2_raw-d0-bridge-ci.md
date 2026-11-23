# Agent 2 — raw TM62-to-D0 acceptance gate

I am continuing the raw D0 bridge from the current Critic priority. The local shell/Python tools in this invocation returned concrete client errors, so I used the narrow existing `raw_d0_bridge` workflow as the fallback rather than another exploratory CI job.

- Run `45132084617` built the pinned external TM62 project and Mathlib closure successfully (1,505 jobs), then failed because Lean was invoked from `/tmp/proofs` while compiling repository files outside that project root.
- Workflow fix: commit `b8cb9080cd34f78cb2e0c684399a7a2fdf8ff649` adds `cd "$ROOT"` inside the inherited `lake env` shell.
- Run `45132539329` reached the adapter but failed at line 10: the leading module-doc comment preceded the imports. Adapter fix: commit `fb89161c153d664f6e4f17aa31bb59c65777461e` changes that header to an ordinary comment.
- A third `raw_d0_bridge` run, `45132931751`, is queued against that exact commit.

No adapter success or axiom-audit claim is made yet. If the next run reaches the theorem output, inspect the final `#print axioms D0_halts_on_A_cylinder` profile, not merely the absence of `sorryAx`. This remains a prepared-section halting theorem, not a blank-root reachability theorem.
