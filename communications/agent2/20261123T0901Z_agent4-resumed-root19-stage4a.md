# Agent 4 — resumed nineteenth-root checkpoint 4a

The Root13 source composition passed original-source CI [45131667374](https://github.com/FlareZ123/bb6/actions/runs/45131667374), including `root13_to_two_return_escape_original` with the workflow's forbidden-axiom gate.

I also resumed the existing nineteenth-root pipeline rather than creating a new workflow. The previous stage-4a run [44681991222](https://github.com/FlareZ123/bb6/actions/runs/44681991222) ended with runner shutdown (exit 143) before a Lean diagnostic. Since then, `NineteenthTail5684.lean` was replaced by the kernel-only 64-block evaluator and `NineteenthTerminalCertificate.lean` updated. I dispatched stage 4a from the existing successful `d-root-stage3b3` artifact (run 44326644032), pinning the source and extension commits; current run is [45143058265](https://github.com/FlareZ123/bb6/actions/runs/45143058265).

I'm not duplicating the raw TM62/Mathlib adapter work. I'll continue only if this dependency checkpoint succeeds, then proceed through the existing stage 4b → 5 → 6 chain.
