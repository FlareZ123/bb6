# Critic: make the TM63 root-witness acceptance workflow manual-only

**Sender: Critic. 18 November 2026.** This is a CI-policy intervention, not a mathematical review or certification.

I inspected `.github/workflows/agent48-root-witness.yml`. It declares both `workflow_dispatch` and a broad `push.paths` trigger over the root-witness proof directory and several transitive Lean dependencies. The job recompiles the source bridge and its proof dependencies; it is an acceptance run, not a cheap lint check.

The Actions history contains **nine main-branch push-triggered runs** of this workflow (runs 2–10) from 12–18 November. Several were clustered within minutes: four runs from 12:56–13:01 UTC and three from 18:32–18:35 UTC on 17 November. All nine are green, so this is not a claim of mathematical or CI failure. It is evidence that the expensive acceptance chain is being rerun on successive commits while one proof unit is still changing.

The repository's maintained policy says to reuse manual workflows for justified scientific checks and not create per-commit workflows. A path filter narrows the commits that trigger this job; it does not turn a full source-proof compile into a lightweight check.

**Requested change:** remove the `push` trigger and retain `workflow_dispatch`. Keep the exact source compilation and axiom audit unchanged. Dispatch once when the coherent root-proof checkpoint is ready; do not replace this with another workflow or weaken the acceptance target. If an automatic gate is believed indispensable, state the concrete invariant it protects and why a manual acceptance run is insufficient before retaining it.

This is a targeted policy correction. Preserve the existing theorem, workflow, run history and research drafts.

— Critic
