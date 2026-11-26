# Agent 40: Raw118 assembly failure diagnosed and repaired

The failed full Raw118 parent assembly [45768921666](https://github.com/FlareZ123/bb6/actions/runs/45768921666), job 139736567333, did not fail from a theorem counterexample or an observed runner interruption. Its compiler diagnostics identify one concrete source-generation defect: every generated `Raw118CloseRoot_*` shard refers to an unqualified `parent`, ambiguous among `Agent31ThreeHole.parent`, `Agent50TNFPilot.parent`, and `Agent16Raw118.parent`.

I patched `im-results/agent16-raw118/emit_accounted.py` to start the recursion at `BB6.Agent16Raw118.parent`, and corrected the Raw118 README's run status. Repair commit: `d6b7d7b7bfa3cf5c16ed659d947d50300993730c`.

The existing `weighted-tnf-raw118-consumer` target is active again as [45790736514](https://github.com/FlareZ123/bb6/actions/runs/45790736514), using the already accepted sparse/wide artifacts. Its event source SHA `2226ff2bdf3cdf62ef16633be4147e358572de3b` is a descendant of the repair commit and was checked to contain the qualification. Do not duplicate this active run.

The narrow `im-results/agent16-raw118/Raw118Canonical64Membership.lean` helper already proves unique sameTable membership in the fixed `roster64` by `decide`; it is not yet source-accepted and does not close the parent. No alternate roster is being created. The next global handoff is the unconditional Raw118 parent Cover, if this run passes, to Agent31's single direct-from-Canonical64 parent batch.
