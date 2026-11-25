# Raw139 source-connected Cryptids leaf pilot

**Status: Lean integration draft; acceptance pending.** This is intermediate work and belongs in `im-results/`, not `results/`.

## Candidate

At Cryptids commit `3647718b5df22e1a61462dec0376bd204526285a`, the module

`BusyBeaver.BB6.NonHalt.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH`

exports `is_not_halt`. Its theorem is proved from the upstream Counter calculus using
`Counter.does_not_halt_of_conj_stem` and the source theorem for
`M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH`.

The corresponding RLE with the halt marker erased is

`1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---`.

It is not an exact row of the dated
`resources/BB6_holdouts_663_2026-10-16.txt` inventory. The source theorem is
upstream evidence; the local adapter and frontier graft remain unaccepted until
the exact Lean 4.36.0-rc2 import closure and axiom audit pass.

## Literal table and first-hole trace

In A0,A1,...,F1 order, the candidate's ordinary moves are:

| Slot | Move |
|---|---|
| A0 | 1RB |
| A1 | 0LE |
| B0 | 1RC |
| B1 | 0RC |
| C0 | 1LD |
| C1 | 0RB |
| D0 | 1LA |
| D1 | 0LE |
| E0 | 1LD |
| E1 | 1LF |
| F0 | 1LD |
| F1 | halt |

The independently replayed first-use schedule, with the initial A0 query at
time zero omitted from the list, is:

`B0@1, C0@2, D1@3, E1@4, F0@5, D0@6, B1@8, C1@9, E0@25, A1@27`.

Thus the unique unqueried transition is F1. The source `IsNotHalt` theorem
implies that every one of the 25 ordinary completions of this one-row leaf
is nonhalting, once the local table and tape-semantics transfer are checked.

The first divergence from the champion's path occurs at E1 = 1LF. The exact
candidate parent is

`championChild 1 ⟨true,false,5⟩`

at the current champion-frontier address

`[D1=0LE, E1=1LF]`.

## Frontier refinement

`Raw139CryptidsLeafPilot.lean` is intended to establish all of the following
in one Lean 4.36.0-rc2 compilation:

1. exact equality between the upstream machine and the local 12-slot table;
2. transfer of upstream `is_not_halt` to local `NeverHalts`;
3. the unique F1 hole and checked first-hole schedule;
4. a weighted nonhalting certificate for the 25-completion leaf;
5. a six-edge `RootedFrontier` from the exact E1=1LF parent, with every
   off-path ordinary sibling retained and halt siblings charged by
   `pathOKB`;
6. exact membership and uniqueness of the E1=1LF parent in the current
   102-entry raw139 residual list;
7. a conditional exact-BB6 consumer replacing only that parent by its
   explicit descendants.

This does **not** prove the whole E1=1LF parent nonhalting, nor does it close
the other canonical parents or the new sibling residuals. The global theorem
remains conditional on covers for all those remaining obligations.

## Reproduction

The existing manual workflow
`.github/workflows/agent6-champion-residual.yml` has an optional
`raw139_cryptids_leaf` target. It checks out the exact Cryptids commit,
aligns its Lake project to Lean 4.36.0-rc2, builds the source theorem, and
runs `reproduce.sh` against the canonical77 and champion-residual build
artifacts. The script records the Lean output and theorem axiom profiles.

Acceptance is pending until that workflow succeeds and the artifact confirms
the current-list membership/address checks. A failed or unrun CI result must
not be described as a locally accepted proof.
