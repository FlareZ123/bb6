# q0 held-leaf BlockFAR search

This directory records a targeted attempt to discharge unresolved one-hole leaves from the q0 source-queue batch using the existing three-cell BlockFAR generator.

**Status: candidate discovery, not yet a complete verified result.** A successful saturation in the independent probe is not itself a theorem. A leaf is treated as proved nonhalting only after the repository generator emits Lean and the Lean 4.36.0-rc2 kernel checks the generated `never` theorem. For `flip=true`, the mirrored-machine theorem is insufficient until `MirrorTransport` also checks `never_original`.

## Candidate tables

The q0 batch has nine held one-hole tables. The following configurations saturated in the local port of the `generate_multi.py` saturation core. Counts below are raw saturation counts before any generator-side quotient/minimization.

| Offset | Partial table | Width | Cap | Mod | Runs | Flip | Left states | Nodes | Edges |
|---:|---|---:|---:|---:|---:|---|---:|---:|---:|
| 0 | `1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA` | 3 | 2 | 4 | 5 | false | 1,565 | 10,166 | 490,760 |
| 300 | `1RB0LC_1RC1RE_1LA0LD_0RA0LB_0RF---_0RB1RA` | 3 | 2 | 4 | 7 | false | 379 | 1,918 | 2,857 |
| 400a | `1RB---_1RC1RD_0LB0RF_0LE1LD_0LC1LB_0RA0RF` | 3 | 2 | 4 | 8 | false | 765 | 3,353 | 3,763 |
| 400b | `1RB1LA_1RC1RD_0LB0RE_0LE0RF_---1LA_1RA1RC` | 3 | 2 | 4 | 2 | true | 7 | 61 | 137 |
| 700 | `1RB0RA_1RC1LB_1LB0LD_0LE0LD_1RE1LF_---1RA` | 3 | 2 | 4 | 4 | false | 790 | 3,985 | 12,105 |
| 2700 | `1RB0LD_1LC1RA_1LE1LA_---0RB_1RE0RF_1RF0LC` | 3 | 2 | 4 | 5 | false | 701 | 2,966 | 4,921 |
| 2800 | `1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---` | 3 | 2 | 4 | 2 | false | 220 | 1,831 | 8,717 |

No saturation was found for offsets 600 or 3500 in the parameter sweeps recorded so far. This is not evidence that no certificate exists.

Offset 700 also saturated with runs=3, 5, 6, and 7; runs=4 had the lowest edge count among the tested runs values. Offset 300 also saturated with runs=8. Offset 400b also saturated with width=2, cap=2, mod=4, runs=2, flip=true, but the width-2 Lean support modules are not present in the current BlockFAR directory, so the width-3 mirrored construction is the actionable candidate.

## Verification workflow

`.github/workflows/agent5-q0-held-blockfar.yml` is a reusable manual workflow. It accepts the partial table, module name, width, cap, modulus, runs, and flip flag; it invokes the repository's `generate_multi.py`, compiles the generated Packed and Proof modules, and uploads the generated source, oleans, and kernel log.

For `flip=true`, the workflow additionally compiles `MirrorTransport.lean` and a generated consumer theorem. The transport lemma reflects the primitive configuration by
`(q,l,r) ↦ (q, tail r, cons (r 0) l)`, reverses every transition direction, proves step/run equivariance, and transfers nonhalting from the mirrored table to the original table.

## Research interpretation

A checked `never` theorem for a one-hole partial table proves that its undefined transition is unreachable from blank tape. It therefore discharges the entire completion cylinder below that partial table. This is the useful connection to the source-queue and rooted-residual coverage projects; it is not by itself an exact BB(6) result.

Offsets 2700 and 2800 are children of the `firstOneB0_1LC` parent (they fix A0=1RB and B0=1LC). Offsets 0, 300, 400a, 400b, 600, and 700 fix A0=1RB and B0=1RC, so they belong under the corresponding B0=1RC parent. Check compatibility against the current parent-cover remainder before subtracting any new cylinder; queue membership alone is not a cover proof.

## Current verification runs

Run IDs and outcomes are maintained in the conversation/Actions history and should be updated here only after the corresponding Lean proof has completed. A failed generator or compilation attempt must not be described as a mathematical result.


## Verified outputs and pending runs (2026-11-25)

Two generated nonhalting certificates have passed Lean CI:

- Offset 300: workflow run [45580723979](https://github.com/FlareZ123/bb6/actions/runs/45580723979), artifact `q0-held-blockfar-Q00300-runs-7` (ID `15007077503`, 689,170 bytes). This is a direct certificate for the original partial table.
- Offset 400b: workflow run [45581935636](https://github.com/FlareZ123/bb6/actions/runs/45581935636), artifact `q0-held-blockfar-Q0400B-runs-2` (ID `15006473349`, 94,149 bytes). This includes the mirrored certificate and the kernel-checked `never_original` transport theorem.

The following direct-certificate runs were still compiling at the last status check:

- Offset 2700: run `45580679383`.
- Offset 400a: run `45580736857`.
- Offset 700: run `45580752871`.

The canonical-parent membership audit is run `45583404503` and was still in progress. Earlier audit attempts failed on workflow setup only; the current run uses the corrected unpack output path and Lean executable path. No parent membership should be assumed until this audit returns its computed matches.
