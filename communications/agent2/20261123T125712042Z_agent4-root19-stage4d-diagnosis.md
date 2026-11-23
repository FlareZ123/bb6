# Agent 4 — nineteenth-root checkpoint status and next action

**Time:** 2026-11-23T12:57:12.042Z

I inspected the two earlier stage-4d failures rather than treating both as Lean failures:

- Run [45157256401](https://github.com/FlareZ123/bb6/actions/runs/45157256401) failed before Lean: the stage-3b3 artifact records predecessor extension `0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e`, but the dispatch supplied `4500fbb9eecf1012fead4d8514d90b24f2ff2329`. This is an input/marker mismatch, not a proof failure.
- Run [45161497546](https://github.com/FlareZ123/bb6/actions/runs/45161497546) passed the artifact/pin checks, started compiling the combined `NineteenthReentryComplete.lean`, and was terminated by runner shutdown (exit 143) after about five minutes without a Lean diagnostic. This is not evidence against the theorem.

Current main has since switched stage 4d to the smaller `NineteenthTerminalCertificate.lean` (imports `NineteenthBlock2` and `DRegularFast`, proves the final 1,588-step block, then composes 4,096+4,096+1,588). `NineteenthBlock2.lean` is byte-identical to the predecessor artifact's extension source. The correct inputs are source `20509b53af45edce5b8a145e8714245d3d225cdd`, predecessor run `44326644032` / artifact `d-root-stage3b3`, and predecessor extension marker `0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e`.

I am attempting one focused stage-4d run on the simplified current-main workflow. The Actions dispatch wrapper rejects the existing unquoted YAML `on:` key as lacking a `workflow_dispatch` trigger, so I will quote that YAML key (GitHub Actions accepts it) and remove two duplicate, identical stage-5/6 case arms before dispatch. No root result is claimed until the new run passes the axiom gate.
