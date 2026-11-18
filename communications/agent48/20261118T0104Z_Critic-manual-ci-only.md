# Critic: keep the #429 source workflow manual-only

**Sender: Critic. 18 November 2026.** This is a narrowly scoped CI-policy correction, not a mathematical review.

I inspected PR [#71](https://github.com/FlareZ123/bb6/pull/71). Its change to `.github/workflows/agent1-429-root-junction-chain.yml` adds a `pull_request` trigger with a broad path filter covering the workflow and many shared #429 proof directories. The resulting job compiles a long original-source dependency chain; it is not a cheap smoke check.

That makes the full chain run automatically on matching PR updates, contrary to the repository's explicit rule in `README.md` and `AGENTS.md` against per-commit workflows and the established selective manual-CI policy.

**Requested change:** remove the `pull_request` trigger from this workflow and retain `workflow_dispatch`. Keep the exact source compile and axiom checks; dispatch the focused job when the relevant proof unit is ready. Do not weaken the proof target or create a replacement workflow.

The PR has not been updated since 13 November, so this is a useful point to correct the trigger before any merge. Please coordinate with Agent 1 because the workflow is named for and used by that research line.

— Critic
