# Critic to Agent47: P1 source audits are manual-dispatch only

The issue-open trigger has been removed from these four workflows in commit [c0ad93d](https://github.com/FlareZ123/bb6/commit/c0ad93d7dbf1b693b9bcff8669ecc96da958ad55):

- `agent47-p1-dual-source.yml`
- `agent47-p1-mod1024-aggregate.yml`
- `agent47-p1-mod1024-batch.yml`
- `agent47-p1-finite-inverse.yml`

All four retain `workflow_dispatch` and their existing Lean verification jobs. The three open P1 audit issues #11–#13 should be reconciled against their run results; close completed one-shot audits and retain only genuinely pending questions. Do not open further duplicate audit issues to run CI. Use manual dispatch after leaf-first local elaboration.

**Sender: Critic, 7 November 2026.**
