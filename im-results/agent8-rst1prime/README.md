# Rst1' counted reset-core investigation

## Candidate itinerary

Input family: `s1Config L 0 1 a 0 b h` in the source S1 encoding.

The observed TM63 trace has ten phases:

| Phase | Operation | Steps |
|---|---|---:|
| 1 | left sweep of `3a+1` | `9a+3` |
| 2 | fixed bridge | `8` |
| 3 | left sweep of `3L+5` | `9L+15` |
| 4 | fixed bridge | `20` |
| 5 | right sweep of `L+1` blocks | `3L+3` |
| 6 | fixed bridge | `9` |
| 7 | right sweep of `a+1` blocks | `3a+3` |
| 8 | fixed bridge | `6` |
| 9 | right sweep of `b` blocks | `3b` |
| 10 | fixed bridge | `30` |

Total primitive steps: `97 + 12*(L+a) + 3*b`. The endpoint head is `h+5+3*b`.

The candidate target family is the source S1 configuration with parameters `L+a+2`, `R=(2^(L+2)-1)*2^a-1`, marker `2`, right unary parameter `b`, value `2^b-1`, and final right parameter `0`, at head `h+5+3*b`. This endpoint equality is not yet formally proved in this directory.

## Fixed bridge traces

All windows and marks below are head-relative. Each start configuration has state D (state index 3) and head 0. `CountedRst1Prime.lean` gives finite traces and a generic source-connected frame lifting theorem.

| Steps | Window | Start marks | End head/state | End marks |
|---:|---:|---|---|---|
| 8 | `[-3,0]` | `[-1]` | `-2 / D` | `[0,-2,-3]` |
| 20 | `[-5,3]` | `[-3,-2,-1,2,3]` | `4 / D` | `[1,0,-1,-3,-4,-5]` |
| 9 | `[-2,2]` | `[0,2]` | `3 / D` | `[0,-1,-2]` |
| 6 | `[-1,3]` | `[2,3]` | `4 / D` | `[1,0,-1]` |
| 30 | `[-3,5]` | `[-3,0]` | `-4 / D` | `[-2,-1,0,3,4,5]` |

The local windows are parameter-independent in the raw simulator. The finite `fRun` computations are intended to be checked by Lean `decide`; the generic `bridgeAt` lifts them through `run_frame` and `shift_run` once the actual tape agrees on the window.

## Current proof status

- The itinerary and cost identity are computationally discovered; they are not yet a theorem about all parameters.
- `CountedRst1Prime.lean` contains `finiteHeads`, `finiteBridgeFrame`, `bridgeAt`, and the five finite bridge traces.
- The main missing obligations are the counted-sweep preconditions, the five source-level window-agreement lemmas, and the final equality of the post-bridge tape with the target S1 encoding.
- The new module is wired into `.github/workflows/agent48-champion-root.yml`, which remains manual-only. Do not restore push triggers; Critic's CI policy is to dispatch expensive source audits manually.
- No `sorry` is intended. The module has not yet been compiled in CI in this invocation.

## Next steps

1. Obtain a manual Lean CI run and repair any elaboration errors in the bridge framework.
2. Prove the closed-form cell behavior of `sweptLeft` and `sweptRight` needed to establish the phase boundaries.
3. Derive the initial S1 left/right cell facts and prove the five bridge-window matches and all five counted-sweep preconditions.
4. Prove the final tape equality to the target S1 configuration, then compose the phase runs with `run_append` and the exact cost arithmetic.
5. Coordinate with Agent 46, who previously selected the Rst1' reset-core edge, to avoid duplicated proof work.