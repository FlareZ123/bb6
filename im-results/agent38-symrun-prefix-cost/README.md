# SymRunEngine initial primitive-time replay (F424 and F412)

**Status: reproducible computational intermediate result.** This dossier isolates the initial `runElemFast` phase in two pinned upstream Cryptids halting certificates. It does not compute either complete halting time and is not a Lean theorem.

## Result

| Machine | `runElemFast` parameters | `stepElemM` iterations | Primitive cost in `runElemFast` | Entry cost | Known prefix total |
|---|---:|---:|---:|---:|---:|
| F424 | (1, 1, 11, 4) | 19,217 | 164,368 | 18 | **164,386** |
| F412 | (7, 3, 11, 4) | 19,255 | 145,981 | 1 | **145,982** |

The branch-cost sums are exact outputs of the deterministic replay relative to the upstream `HasSymRunRules` branch-cost equations, but are not yet a Lean-certified cost theorem. The entry costs are `init_to_CB` = 18 for F424 and `init_to_BB` = 1 for F412. Thus the replayed initial-prefix totals are 164,386 and 145,982. For the combined exponent bounds, a coarse formal upper bound below 2^21 for either prefix is sufficient. The separate terminal `step_DL_zero_halt` costs 1 after the final `stepSym` state.

## Cost equations extracted from the proof source

Pinned source: `google-deepmind/cryptids` commit `3647718b5df22e1a61462dec0376bd204526285a`.

The common `stepElemM` branch costs, in source theorem order, are:

- `step_BB_nil`, `step_BB_zero`: 1 each;
- `step_BB_run0`: 8 (F424), 6 (F412);
- `step_BB_run1`, `step_DL_run1`, `step_CB_run1`: 3 each;
- `step_BB_run2`, `step_CB_run2`, `step_CB_run_ge3`: 5 each;
- `step_BB_run3`, `step_BB_run_ge4`: 9 each;
- `step_DL_run0`: 1;
- `step_CB_nil`, `step_CB_zero`: 2 each;
- `step_CB_run0_nil`, `step_CB_run0_zero`: 3 each;
- `step_CB_run0_run0`: 6.

Two branches invoke the helper theorems `cyc_R_A` and `exit_R_A`. Their costs are 3 per cycle and 13 (F424) / 11 (F412) for the exit. Consequently:

```
step_DL_run2(d0)       = 6 + 3*(d0+1) + exit_R_A
                       = 3*d0 + 22   (F424)
                       = 3*d0 + 20   (F412)

step_CB_run0_run_pos(d2) = 5 + 3*(d2+1) + exit_R_A
                         = 3*d2 + 21 (F424)
                         = 3*d2 + 19 (F412)
```

The `strictNat` wrappers in `HaltShared.lean` are definitional identity wrappers, not additional machine-step loops. The source transition cases in `stepElemM` are translated directly by the script.

## Independent replay checks

The script `symrun_prefix_cost.mjs`:

1. executes the exact number of `stepElemM` updates specified by `runElemFast`;
2. accumulates the machine-specific branch costs above;
3. records every branch count and cost contribution;
4. checks that the final decoded configuration equals the source module's `initSymCyc3` state for each machine.

Both final-state checks pass. The F424/F412 prefixes reach the same left symbolic tape (including the `repB1 46` expansion); their right tapes differ by one trailing `.run 1`, exactly as in the two source declarations.

The replay also records the maximum run parameter and decoded list length seen during this initial phase. Those are finite-prefix observations only; they are not bounds for the later `stepSym` trajectories.

Run with:

```sh
node symrun_prefix_cost.mjs
```

## Remaining timing obligation

The subsequent `stepSym` trajectories contain 70,511 macro iterations for F424 and 21,383 for F412. Those macro counts are not primitive TM steps. A complete bound still requires a cost-indexed account of `sweepBB`, `sweepCB`, `tryRuleA`, `tryRuleB`, `tryRuleBC`, and their helper contractions, followed by accumulation along the checkpointed traces.

No exact full halting time, comparison against the BB(6) champion, or global BB(6) conclusion is claimed here.
