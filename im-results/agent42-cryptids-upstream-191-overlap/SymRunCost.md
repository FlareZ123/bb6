# Primitive-time extraction for the SymRunEngine halt proofs

Status: research lead only; no primitive-step bound has been proved or computed.

Pinned upstream source: `google-deepmind/cryptids` commit `3647718b5df22e1a61462dec0376bd204526285a`, `BusyBeaver/Calculi/HaltShared.lean`.

## Scope

Two of the five exact-overlap `IsHalt` modules use `BusyBeaver.SymRunEngine`, not `RleStackEngine`:

- F424: rooted RLE `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---`, module `BusyBeaver/BB6/Halt/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean`.
- F412: rooted RLE `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA`, module `BusyBeaver/BB6/Halt/M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.lean`.

The final halt lemma in both is `step_DL_zero_halt`, whose proof contains `execute 1`. Their initial entry proofs differ: F424's `init_to_CB` uses `execute 18`; F412's `init_to_BB` uses `execute 1`.

## Exact symbolic iteration counts

In `HaltShared.lean`:

- `stepSym16` is 16 iterations of `stepSym`;
- `stepSym256` is 16 iterations of `stepSym16`;
- `stepSym4096` is 16 iterations of `stepSym256`;
- `runElemFast a b c d` performs (d) iterations of `stepElem4096), then (c) of `stepElem256), then (b) of `stepElem16), then (a) of `stepElemM).

Thus the initial `runElemFast` macro counts are:

| Module | Parameters `(a,b,c,d)` | Underlying `stepElemM` iterations |
|---|---:|---:|
| F424 | (1,1,11,4) | (1+16+11·256+4·4096=19,217) |
| F412 | (7,3,11,4) | (7+3·16+11·256+4·4096=19,255) |

The subsequent `stepSym` chunks are:

| Module | Checkpoint progression | Symbolic `stepSym` count |
|---|---|---:|
| F424 | `initSymCyc3 → symChk4096 → … → symChk69632 → symChk70511` | (17·4096+3·256+6·16+15=70,511) |
| F412 | `initSymCyc3 → symChk4096 → … → symChk20480 → symChk21383` | (5·4096+3·256+8·16+7=21,383) |

Total high-level macro iterations (initial `runElemFast` plus `stepSym`) are 89,728 for F424 and 40,638 for F412. These are **not primitive TM step counts**.

## Machine-specific primitive rule costs

The two modules have 23 visible `execute n` invocations each. Their first 21 source-order counts (the `HasSymRunRules` rule proofs) are:

- F424: `[1,1,8,3,5,9,9,3,13,1,3,6,2,2,3,3,6,5,3,5,5]`
- F412: `[1,1,6,3,5,9,9,3,11,1,3,6,2,2,3,3,6,5,3,5,5]`

The final two invocations are the initial entry proof and `step_DL_zero_halt`: `[18,1]` for F424 and `[1,1]` for F412. The base rule costs differ in two places, so a shared symbolic cost development must be parameterized by the machine's `HasSymRunRules` instance. The arrays above are in source order; map them to theorem names before using them in a proof.

## Cost-indexed proof route

`stepSym_sound` currently proves only `StepStar`:

- `BB` mode uses `sweepBB_sound`;
- `DL` mode uses `stepElemThenBB_sound`;
- `HALT` is reflexive;
- `CB` mode composes `sweepCB_sound` and `afterSweepCB_sound`.

`runElemFast_sound` composes the four iterated `stepElem*` soundness lemmas. As with the RLE engine, a `StepStar` proof does not retain a usable numeric length. A parallel `ReachWithin` / `StateHaltsWithin` development is needed:

1. Define a state-dependent primitive cost for `stepElemM` and `stepSym`, derived from `stepElemM_sound` / `stepSym_sound` branch proofs and the module's `HasSymRunRules` costs.
2. Port the deterministic `stepElemM` / `stepSym` state updates and accumulate those costs over the actual F424/F412 traces.
3. Validate the port against the explicit `symChk*` states before treating the accumulator as computational evidence.
4. Add the fixed initial and final costs (`18+1` for F424, `1+1` for F412), then transfer exact `multiStep` counts via upstream `multiStep_toBB` and the local `source_halts_after_iff_agent8_halts_after` adapter.

The checkpoint names and arithmetic above are established from the upstream proof source; no primitive-step upper bound is asserted here.
