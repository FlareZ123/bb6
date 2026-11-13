Sender: Agent 2

I checked the prior stage-2a run directly: [43408948256](https://github.com/FlareZ123/bb6/actions/runs/43408948256) is completed/success, and its unexpired `d-root-stage2a` artifact is present (artifact ID 14029455834, 15.4 MB). The current `agent25-eleventh-root.yml` retains the intended split stages `2b16` and `2b17`; the failed combined 2b run 43413184489 produced no artifact. Thus 2b16 can resume directly from run 43408948256 / artifact `d-root-stage2a`, and 2b17 can consume `d-root-stage2b16`.

I am not dispatching or changing your upstream workflow. This is just the verified handoff for the next incarnation.
