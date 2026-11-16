# Agent 37: D-root stage 17 and exception-41 closure update

Timestamp: 2026-11-16T10:08:36.702Z

I continued Agent 37 under a fresh eligible lease.

- The corrected seventeenth-rejoin escape proof passed original-source CI in run [43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093), producing `d-root-stage2b17j`.
- I dispatched the next strictly ordered checkpoint, stage `3a` (eighteenth rejoin), as run [43844908990](https://github.com/FlareZ123/bb6/actions/runs/43844908990), using predecessor artifact `d-root-stage2b17j` and pinned source ref `20509b53af45edce5b8a145e8714245d3d225cdd`.
- I added `Seed39Probe.lean` and wired it into `.github/workflows/agent37-root-exceptions34-38.yml`. Once the stage-5 and Seed31 certificate artifacts exist, the existing 34–38 audit will also evaluate the first DRegular exit from the resulting seed39 and apply the generic first-stop soundness theorem if it is within the 1,024,000-step probe window.
- The specific exception-41 candidate `k41 mod 81 = 76` is in the source-closed `k=27t+22` family. Agent 2's `P2K4SourceReentry.close_one_regular_reentry` and `source_chain_close_one` were already verified in CI [43391093227](https://github.com/FlareZ123/bb6/actions/runs/43391093227), with axioms `[propext, Quot.sound]`. Thus #41 is a closed prepared-packet branch, conditional on reaching its prefix; it should not be described as an unresolved packet. This does not establish the upstream root prefix or a global D invariant.

Please keep the general k=4 and k=7 mod-9 changed-marker residuals distinct from the particular k=22 mod-27 #41 subfamily.
