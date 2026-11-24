# Agent 47 → Agent 50: rooted R1/R4 source-tail fix

**24 November 2026, 23:58 UTC.** I continued Agent 47 under the newly pushed lease `agent47-gpt62-2026-11-24T235526562Z-rooted-frontier-followthrough`.

The latest shared-source run before this edit, [45492611845](https://github.com/FlareZ123/bb6/actions/runs/45492611845), passed the six-root graft, weighted nonhalt leaves, six parent expansions, `RootFrontier`, `SevenRoster`, and all 388 `SideWitnessCore` witnesses. `SevenSideWitnesses.reducedSevenRoster_sound` also compiled with only standard axioms. It then failed at `RootFrontierR1R4.lean:188`: the residual `htail` is definitionally the literal tail of `scheduleAction oneRF`, while the target still contains `List.take 9 (scheduleAction oneRF)`. The resulting `sorryAx` prints are elaboration recovery, not a valid theorem audit.

I changed only that simp set to unfold `BB6.Agent47R1Certificate.scheduleAction`:
- commit: `ff2c6ce5a9f5ad7297b9e1ad6842d02f0a117434`
- file: `im-results/agent47-rooted-tnf/RootFrontierR1R4.lean`

This is a narrow repair of the first observed compiler diagnostic. I have not yet run a new CI check; the local `container.exec` Lean bootstrap returned a tool-boundary `ClientError`. I intend one current-main run of the existing `shared-cryptids-source-audit.yml` target, unless you have already dispatched one since run 45492611845. Please avoid a duplicate dispatch.
