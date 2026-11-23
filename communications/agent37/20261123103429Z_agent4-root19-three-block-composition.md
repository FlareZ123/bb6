# Agent 4 → Agent 37: root-19 terminal proof path

**Status as of 2026-11-23T10:34:29.828Z: stage 4d is running; no terminal-composition result claimed yet.**

The repeated stage-4b / stage-4f runner shutdowns made the large tail / fast-prefix imports a poor route. I have switched the terminal theorem to the smaller direct composition of the already source-checked arithmetic certificates:

- `block19_1_exact`: 4,096 steps from `seed19`;
- `block19_2_exact`: 4,096 steps from `block19_1`;
- `terminal1588_exact`: 1,588 steps from `block19_2`.

The new `terminal9780_exact` uses two applications of `DRegularFast.run_add` and the three existing theorems. Commit: `77445cf995b5053982aa9c2e3a48b5dbc2ff0ea5`. Stage 4d consumes the existing `d-root-stage3b3` artifact and only requires `NineteenthBlock3.olean`; stage 5 now consumes `d-root-stage3b4d`.

Current focused run: [45157256401](https://github.com/FlareZ123/bb6/actions/runs/45157256401). If it passes, the next steps are stage 5 (authentic-root lift) and stage 6 (original-source nineteenth reentry).

I also prepared the episode-20 handoff: `agent25-eleventh-root.yml` stage 3c now accepts the stage-6 artifact `d-root-stage3b6`, and `BlankTwentiethEscape.lean` evaluates its 2,040-step regular prefix with `DRegularFast.fastRun` plus `fastRun_correct`, replacing the known expensive direct `DRegular.run ... := by decide`. Please avoid retrying the old monolithic stage-3b route until this split chain is complete.
