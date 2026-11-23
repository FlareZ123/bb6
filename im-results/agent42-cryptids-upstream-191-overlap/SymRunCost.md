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

### F424 repeated-block sweep costs (Lean draft)

The F424 cost pilot now includes exact `ReachesIn` constructions, by induction on the repeat count, for all six repeated-block sweeps:

| Sweep | Primitive cost | Per-block derivation |
|---|---:|---|
| `sweep_BB_B1_exact` | `11k` | BB-run0 (8) + BB-run1 (3) |
| `sweep_BB_C2_exact` | `14p` | BB-run1 (3) + BB-run0 (8) + BB-run1 (3) |
| `sweep_BB_C12_exact` | `25m` | BB commutation (14) + BB/B1 transfer (11) |
| `sweep_CB_B1_exact` | `21k` | CB-run0-run-positive with parameter 0 |
| `sweep_CB_B2_exact` | `24p` | CB-run0-run-positive (21) + CB-run1 (3) |
| `sweep_CB_B12R_exact` | `45m` | two CB-run0-run-positive steps (21 each) + CB-run1 (3) |

The corresponding witnesses are in `SymRunCostedStepPilot.lean`, together with the exact 3-step F424 CB-run1 witness and the 11-/14-step BB compositions. These are source-aligned proof drafts, not accepted results: no Lean compile has been obtained for this invocation, and the exact imported-source RC2 preflight remains outstanding. The coefficients match the independent F424 rule-cost table above; F412 still needs its own machine-specific witnesses because its variable atomic costs differ.

## Cost-indexed proof route

`stepSym_sound` currently proves only `StepStar`:

- `BB` mode uses `sweepBB_sound`;
- `DL` mode uses `stepElemThenBB_sound`;
- `HALT` is reflexive;
- `CB` mode composes `sweepCB_sound` and `afterSweepCB_sound`.

`runElemFast_sound` composes the four iterated `stepElem*` soundness lemmas. As with the RLE engine, a `StepStar` proof does not retain a usable numeric length. A parallel `ReachWithin` / `StateHaltsWithin` development is needed. The F424 pilot now drafts the first local stage: all atomic rule witnesses, all six repeated-block sweep witnesses, constructor-complete `stepElemBB_within` / `stepElemDL_within` / `stepElemCB_within`, and `stepPure_within` with budget `50*(M+1)`. These statements use a local maximum-field measure and remain uncompiled. The remaining route is:

1. Obtain exact-import Lean 4.36.0-rc2 compilation and audit of the costed pilot, then align its local field measure with the trace-statistics measure.
2. Lift `stepPure_within` through the actual macro/`stepSym` branches, including the outer CB/BB sweep and fallback paths, with exact accumulated primitive costs.
3. Port the deterministic `stepElemM` / `stepSym` state updates and accumulate those costs over the actual F424/F412 traces.
4. Validate the port against the explicit `symChk*` states before treating the accumulator as computational evidence.
5. Add the fixed initial and final costs (`18+1` for F424, `1+1` for F412), then transfer exact `multiStep` counts via upstream `multiStep_toBB` and the local `source_halts_after_iff_agent8_halts_after` adapter.

The checkpoint names and arithmetic above are established from the upstream proof source; no primitive-step upper bound is asserted here.




### F424 costed one-element / stepPure draft

`SymRunCostedStepPilot.lean` now contains the following source-aligned statements:

- exact `ReachesIn` witnesses for all 19 F424 atomic rule branches;
- exact induction witnesses for the six repeated-block sweeps, with costs `11k`, `14p`, `25m`, `21k`, `24p`, and `45m`;
- `stepElemBB_within`, `stepElemDL_within`, and `stepElemCB_within` under the uniform budget `50*(M+1)`;
- `stepPureBB_within`, `stepPureDL_within`, `stepPureCB_within`, and `stepPure_within` under the same budget, where `M` is a local recursive maximum of all numeric fields in the symbolic state.
- `sweepBB_within` with budget `50*(M_L+1)*(|L|+1)`, where `M_L` is the maximum numeric field in the left stack; and `sweepCB_within` with budget `50*(M_R+1)*(|R|+1)`, where `M_R` is the maximum numeric field in the right stack. The CB proof charges only parameters on the consumed right side; the BB proof charges only parameters on the consumed left side.
- The existing `SymRunTraceStats` field-growth theorem is reused through `stepPure_iter_within`, giving an n-iteration budget `50*n*(M+n+1)`.
- `ruleA_step_within` and `ruleA_iter_within` cost the source 66-step A-block and its n-fold iteration; `ruleC_step_within` and `ruleC_iter_within` do the same for the 46-step C-block.
- Rule B's four exact blocks (126, 118, 106, and 98 `stepPure` iterations for AA, AB, BA, and BB separators) now have costed witnesses, with `ruleB_step_within` and `ruleB_iter_within` using the uniform 126-step envelope. Its iteration proof uses a `+4` field-growth bound per block.
- All three rule-family iteration theorems are now present. The remaining gap is the full `tryRuleA`/`tryRuleB`/`tryRuleBC` dispatch composition and the `afterSweepCB` / `stepElemThenBB` wrapper.

The derivation is structural: variable atomic costs are `3d+22` (DL) and `3d+21` (CB); the largest repeated sweep is `45m`; fixed atomic costs are at most 9. All are bounded by `50*(M+1)` when the relevant repeat/run parameter is at most M. Peel-only branches use the fact that `peelPureTok` does not increase the local maximum field.

**Not yet accepted:** the new block has not been compiled. The local container/Python tools returned tool-level ClientErrors during RC2 preflight, and no CI substitute was used. Exact imported-source compilation, endpoint simplification checks, and axiom audit remain mandatory. The remaining outer source-cost gates are `afterSweepCB`, `stepElemThenBB`, and complete `stepSym` branch composition, followed by the initial `runElemFast` prefix. F412 still needs its own rule-cost witnesses and costed branch theorem.
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
2. Compile and audit the exact imported-source versions of `f424_trace_range_certificate`, `f412_trace_range_certificate`, `stepPure_field_growth`, `stepPureIter_field_growth`, `sweepCB_length_bound`, `sweepCB_length_le_564`, `stepElemCB_BB_length_bound`, and `stepElemCB_after_sweep_570`; the source-equivalent preflight is not a substitute.
3. Prove the primitive-cost bound for each `stepPure` branch and cost-indexed source soundness for the six repeated-block sweeps and outer `stepSym` branches. `SymRunCostedStepPilot.lean` now drafts exact `ReachesIn` witnesses for the listed F424 atomic branches, cycle, exit, and two variable-cost rules, plus `ReachesWithin` composition; it remains uncompiled.
4. Prove the source costed transfer for the initial `runElemFast` prefix, including the fixed entry costs; the current (<2^{31}) prefix arithmetic is still a transcription.
5. Preserve the separate final `step_DL_zero_halt` cost +1 and transfer through the exact local machine identity and halting adapter, with axiom audit.

The earlier machine-specific rule arrays and checkpoint arithmetic above remain the source anchors; the Agent 38 dossier supplies the replay and cost-bound candidate rather than a competing account.

## 2026-11-22 source-level proof extensions (not yet accepted)

The previous exact-source RC2 run `44955198218` successfully built the pinned
F424 and F412 upstream modules and reached the local trace-audit file. The
audit failed in the `.run 1` and `.run 2` branches of
`stepElemBB_counter_sum_le`: both used `bumpSymR_counter_sum_le` without
transporting it across the unchanged left suffix. The `.item .zero` and
large-run branches already had the required lift. The two residual branches
now use `Nat.add_le_add_left hR (listCounterSum L1)` followed by arithmetic
discharge. This is a proof-script repair, not a counterexample to the source
transition. **The repair is uncompiled**: local shell and Python execution
still fail at the tool boundary, so no CI dispatch is justified under the
compile-first gate. The prior `sorryAx` report in the sweep theorem is
downstream of these elaboration failures; only a fresh exact-source compile
and transitive axiom audit can determine whether it disappears.

The costed pilot now drafts the missing source-`peelTok` facts:
`pilot_peelTok_field_growth`, `pilot_peelL_field_growth`, and the
length bounds `|peelTok t xs| ≤ |xs|+6`, `|peelL L| ≤ |L|+5`.
These are the exact bounds needed for the DL-to-BB branch; they are not yet
compiled against the imported source.

The pilot also now drafts the 46-step Rule-A prelude
`stateA0 (k+1) (d+6) → stateA 0 k d`. Composing it with n 66-step blocks
gives the explicit primitive-cost bound
`50·66·(n+1)·(M+n+113)`, where M is the initial field maximum. Under
`n ≤ M`, this is at most `379,500·(M+1)^2 < 2^19·(M+1)^2`.
This closes the missing initialization-cost calculation for the successful
Rule-A branch, but not the surrounding `tryRuleA` dispatcher proof.

All additions remain source-level drafts. The local shell/Python execution
tools returned tool-boundary ClientErrors in this invocation, so no local
Lean preflight or exact imported-source acceptance was obtained. Do not
replace the required local preflight with a CI dispatch. No F424/F412
halting-time classification or BB(6) upper bound is claimed.

## 2026-11-22 outer BB/DL branches (source-level, uncompiled)

The costed pilot now contains draft theorems `stepSym_BB_within` and
`stepSym_DL_within`, each proving a `2^13(M+1)` primitive-time bound under
the trace invariant `L.length + R.length ≤ 94`.

- BB: `sweepBB_within` costs at most `50(M+1)(|L|+1) ≤ 50·95(M+1) < 2^13(M+1)`.
- DL: `peelL` is field-nonincreasing and increases length by at most five, so
  `|peelL L|+2 ≤ 101`. A DL element followed by its optional BB sweep is
  bounded by `50(M+1)(|peelL L|+2) ≤ 50·101(M+1) < 2^13(M+1)`.
  The BB-producing DL case is only a leading run-0; its sweep sees the
  unchanged suffix, while the run-2/right-run branch returns CB and does not
  invoke a BB sweep.

The corresponding helper drafts are `stepElemDL_within25`,
`finishThenBB_within`, `stepElemDL_BB_left_bounds`, and
`stepElemThenBB_DL_within`. These Lean declarations have not been locally
compiled or axiom-audited. The CB branch, full `stepSym_within`, and the
initial `runElemFast`/final halting transfer remain open.

## 2026-11-22 CB single-element fallback (source-level, uncompiled)

The pilot now drafts `stepElemCB_run0_within25` and `stepElemCB_within25`, tightening a single CB element transition to `25(M+1)`. It also proves `bumpSymL_length_le` (at most five extra left stack tokens) and, when the CB element transition returns BB, `stepElemCB_BB_left_length` with the safe one-sided bound `|L_out|≤|L|+7`. This accounts for the possible two-token run-0 prefix.

Composing the element transition with its optional BB sweep gives `stepElemThenBB_CB_within` with budget `2^9(M+1)(|L|+8)`. This closes the *single-element fallback wrapper* used by `afterSweepCB`; it does not close the Rule A/B/BC macro-recognition branches. The complete CB branch and full `stepSym` theorem remain open.
