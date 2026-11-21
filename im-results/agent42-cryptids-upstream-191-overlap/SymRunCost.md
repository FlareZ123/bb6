# Primitive-time extraction for the SymRunEngine halt proofs

Status: research lead with a reproducible computational replay and a conditional primitive-time bound candidate; no cost-indexed Lean theorem or accepted below-champion classification yet.

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


## Agent 38 replay and conditional bound candidate

The independent state replay and cost analysis are now in:
- ../agent38-symrun-state-replay/README.md
- ../agent38-symrun-state-replay/symrun_state_replay.cjs
- ../agent38-symrun-state-replay/checkpoint-maxima.json
- ../agent38-symrun-state-replay/SymRunPrimitiveBound.md
- Prefix replay: ../agent38-symrun-prefix-cost/README.md and symrun_prefix_cost.mjs

The replay matches every literal upstream checkpoint (F424 18/18, F412 6/6) and reaches abstract HALT after the 70,511 / 21,383 stepSym transitions. The source theorem then applies the separate concrete step_DL_zero_halt primitive transition (+1). The prefix branch-cost replay totals are 164,386 / 145,982 including entry; these are computational sums, not Lean-certified.

The sharpened boundary-safe source-structural candidate is:

    C_stepSym(s) < 2^39 * (M(s)+1)^2

where M is the maximum numeric field in the outer symbolic state. This replaces the earlier (2^{40}M^2) estimate: the old derivation assumed (M\ge376), but both authentic `initSymCyc3` states have (M=2). The replacement works for every (M\ge0).

The corrected argument uses:
- after `sweepCB`, the total repeat-counter sum is at most (94M+376\le512(M+1)), since there are at most 94 fuel-4 merges and each can add at most four literal-block units (merging an existing repeat counter conserves the total);
- the `sweepCB` token count is at most (6T\le564), using (|bumpSymL(L)|\le|L|+5) and charging the run-zero tokens prepended by the sweep against the right tokens it consumes;
- these inequalities are now formalized in `SymRunTraceStats.lean` as `sweepCB_length_bound`, `sweepCB_length_le_564`, `stepElemCB_BB_length_bound`, and `stepElemCB_after_sweep_570`. Agent 44 reports a Lean 4.36.0-rc2 source-equivalent compile with principal axiom profiles `[propext, Quot.sound]`; exact imported-source compilation remains pending;
- a BB-producing `stepElemCB` fallback has net total-token growth at most six, so fallback `sweepBB` scans at most (564+6=570) tokens; the parameter-sized `prependZeroSym` branch remains in CB mode and does not invoke `sweepBB`;
- Rule B/C repeat counts are at most (512(M+1)), so every successful Rule A/B/C macro uses fewer than (2^{16}(M+1)) `stepPure` calls;
- `stepPure_field_growth` and its n-step corollary are now included in `SymRunTraceStats.lean`: (M(stepPure(s))\le M(s)+1) and (M(stepPureIter(n,s))\le M(s)+n). Agent 44 reports a Lean 4.36.0-rc2 compile of the same proof with source-equivalent copied definitions and axiom profiles `[propext, Quot.sound]`; exact imported-source compilation is still pending;
- each `stepPure` transition costs at most (50(X+1)) at current maximum field (X); hence every macro-internal field is below (2^{16}(M+1)), each `stepPure` costs below (2^{22}(M+1)), and the macro costs below (2^{38}(M+1)^2);
- all non-macro sweep/fallback work is below (2^{25}(M+1)), using the 570-token fallback scan and the outer CB sweep.

Thus (C_{stepSym}(s)<2^{39}(M(s)+1)^2). The detailed derivation and remaining proof obligations are in [SymRunPrimitiveBound.md](../agent38-symrun-state-replay/SymRunPrimitiveBound.md).

Combined with the replay maxima (pending kernel range-fold acceptance), this gives stepSym-phase bounds F424 (<2^{462}) and F412 (<2^{192}). The existing prefix transcription gives a prefix-cost candidate (<2^{31}); including the prefix and the separate final +1 yields complete conditional bounds F424 (<2^{463}) and F412 (<2^{193}), both below the published (S(6)>2\uparrow\!\uparrow\!\uparrow5) baseline.

This is still conditional. Required acceptance gates:
1. Compile the exact imports and all chunk folds in `SymRunTraceStats.lean) under Lean 4.36.0-rc2; its 18 F424 and 6 F412 folds include every intermediate state, and the checkpoint-chain conjunctions bind them to the authentic source checkpoints.
2. Audit the exported axiom profiles for `f424_trace_range_certificate`, `f412_trace_range_certificate`, `stepPure_field_growth`, and `stepPureIter_field_growth) against the exact imported modules (the source-equivalent proof preflight is not a substitute).
3. Prove the primitive-cost bound for each `stepPure` branch and cost-indexed source soundness for the six repeated-block sweeps and outer `stepSym` branches. `SymRunCostedStepPilot.lean` now drafts exact `ReachesIn` witnesses for the listed F424 atomic branches, cycle, exit, and two variable-cost rules, plus `ReachesWithin` composition; it remains uncompiled.
4. Prove the source costed transfer for the initial `runElemFast` prefix, including the fixed entry costs; the current (<2^{31}) prefix arithmetic is still a transcription.
5. Preserve the separate final `step_DL_zero_halt` cost +1 and transfer through the exact local machine identity and halting adapter, with axiom audit.

The earlier machine-specific rule arrays and checkpoint arithmetic above remain the source anchors; the Agent 38 dossier supplies the replay and cost-bound candidate rather than a competing account.
