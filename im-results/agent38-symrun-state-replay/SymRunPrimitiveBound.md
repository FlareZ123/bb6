# Coarse primitive-time bound candidate for SymRun F424/F412

**Status: conditional proof sketch; not yet a theorem.** This note turns the checkpointed state replay and source-derived rule costs into a deliberately loose primitive-time bound. It is intended to be challenged and then formalized with a cost-indexed reachability relation. Do not treat either machine as a certified DecidedBelow leaf yet.

Pinned source: google-deepmind/cryptids commit 3647718b5df22e1a61462dec0376bd204526285a, using BusyBeaver/Calculi/HaltShared.lean and the F424/F412 machine modules.

## Exact primitive costs exposed by the source

Write b0 for the step_BB_run0 cost, b1 = 3 for step_BB_run1, and c1 for the step_CB_run0_run_pos cost at parameter d2 = 0.

| Rule cost | F424 | F412 |
|---|---:|---:|
| b0 | 8 | 6 |
| b1 | 3 | 3 |
| step_CB_run0_run_pos(0) = c1 | 21 | 19 |
| step_CB_run1 | 3 | 3 |
| variable step_DL_run2(d) | 3d + 22 | 3d + 20 |
| variable step_CB_run0_run_pos(d) | 3d + 21 | 3d + 19 |
| all other atomic cases | at most 9 | at most 9 |

The six repeated-block sweep lemmas in HaltShared.lean therefore have these exact costs:

| Sweep lemma | F424 | F412 |
|---|---:|---:|
| sweep_BB_B1(k) | 11k | 9k |
| sweep_BB_C2(p) | 14p | 12p |
| sweep_BB_C12(m) | 25m | 21m |
| sweep_CB_B1(k) | 21k | 19k |
| sweep_CB_B2(p) | 24p | 22p |
| sweep_CB_B12R(m) | 45m | 41m |

For example, sweep_BB_C12 composes step_BB_r1_r0_r1_comm (cost b0 + 2b1) with step_BB_r0_r1 (cost b0 + b1), giving 2b0 + 3b1. The largest coefficient across both machines and all six sweeps is 45.

Let M ≥ 376 bound every run value and repeat counter in an outer symbolic state. Each stepPure case either:
- uses at most one of the six repeated-block sweeps, with counter at most its current internal-state bound; or
- uses one atomic primitive rule, whose cost is at most 3M + 22 when its run parameter is at most M.

Thus, for an internal state whose fields are bounded by M':

    C_stepPure ≤ max(45M', 3M' + 22, 9) ≤ 50(M' + 1).

This local estimate is independent of the number of tokens because one stepPure transition selects at most one sweep lemma.

## Counter aggregation across the outer sweepCB

A first, overly optimistic version of this estimate treated every counter extracted after sweepCB as still bounded by the largest individual input field M. That ignores eatFuel: a sweep can merge several repeat counters from the opposite tape before afterSweepCB dispatches to Rule A/B/C.

The correction is controlled by the sum of counters. The replay gives at most L = 94 symbolic tokens across both tapes, so the initial repeat-counter sum on either tape is at most 94M. Each eatFuel call has fuel 4 and can add at most four literal-block increments; sweepCB makes at most L such calls. Merging preserves the sum of existing counters, so after the sweep any individual merged repeat counter is at most

    94M + 4L ≤ 94M + 376 ≤ 95M < 128M

for M ≥ 376. Thus any repeat counter subsequently extracted by tryRuleA/B/BC is bounded by 128M. The run parameter dispatched by tryRuleA or tryRuleBC is unchanged by the sweep and remains bounded by M.

The same sweep can expand the left token list through bumpSymL. One bump expands at most one repeat token, with at most five additional tokens, and the corresponding branch prepends at most two run0 tokens. There are at most L scanned right-side tokens, so the post-sweepCB left list has at most L + 7L = 8L ≤ 752 tokens. A subsequent stepElemThenBB fallback can add at most eight further tokens before an optional sweepBB; if it creates a long zero prefix via prependZeroSym, that branch remains in mode CB and does not invoke sweepBB. Thus the fallback sweep scans fewer than 760 tokens; use the round bound 1024.

## Cost of one stepSym transition

The source soundness proof factors through sweepBB, sweepCB, stepElemThenBB, and one of tryRuleA, tryRuleB, tryRuleBC.

The six repeated-block sweep coefficients are at most 45. On the original outer state, sweepCB scans at most 94 tokens and costs below 2^13 M. If the subsequent fallback calls stepElemThenBB, its sweepBB scans fewer than 1024 tokens; each repeat counter is below 128M, so its cost is below

    1024(45 × 128M + 24) + 25M < 2^23 M.

Thus the combined outer sweep/fallback work is below 2^24 M. The BB- and DL-mode cases are smaller.

For the successful rule macros, the source soundness lemmas use:

- Rule A: 46 stepPure calls for ruleA0, then 66 per ruleA_iter iteration. Its iteration count m_new ≤ M, so at most 46 + 66M ≤ 112M calls.
- Rule B: one of 98, 106, 118, or 126 stepPure calls per ruleB_iter iteration. Its iteration count n3 ≤ 128M, so at most 126 × 128M = 16,128M calls.
- Rule C: 46 stepPure calls per ruleC_iter iteration. Its iteration count n4 ≤ 128M, so at most 46 × 128M = 5,888M calls.

Hence every successful macro uses at most 16,128M stepPure calls.

The affine iterator updates keep every macro-boundary field below 514M:
- Rule A fields are bounded by 128M at macro boundaries; its micro-sequences have at most 66 steps.
- Rule B starts with p0 ≤ 32, repeat counters at most 128M, and d2 ≤ M. Across at most 128M iterations, p increases by 2 and d2 by 4, so the largest boundary field is at most 513M.
- Rule C starts with counters at most 128M; across at most 128M iterations, k and d2 increase by 2, so the largest boundary field is at most 384M.

Inspection of the stepPure clauses shows that an individual numeric field changes by at most one in one micro-step (the larger affine changes occur only at the macro-iteration boundary). At most 126 micro-steps therefore keep every internal field below 514M + 126 < 1024M, since M ≥ 376.

Each internal stepPure call consequently costs at most

    50(1024M + 1) ≤ 51,250M.

The successful rule macros cost at most

    16,128M × 51,250M
      = 826,560,000M^2 < 2^30 M^2.

Adding the outer work gives the conservative per-transition candidate

    C_stepSym(s) ≤ 2^40 M(s)^2.

The constant 2^40 is deliberately loose. This is a proof target based on the displayed source inductions, not yet a Lean theorem. The key details to make explicit in a formal cost semantics are the repeat-sum invariant through eatFuel, the post-sweep token bound, and the unit-change bound for the stepPure micro-sequences.

## Concrete trace maxima and resulting candidate bounds

The independent replay matches every literal upstream checkpoint and reaches the final HALT state:

| Machine | stepSym calls | Maximum field M | Bit length | Bound from 2^40 M^2 per call |
|---|---:|---:|---:|---:|
| F424 | 70,511 (< 2^17) | 12,464,561,897,144,001,482,331,935,594,779,263,804,489,570,179,353,031,112,091,137 | 203 | < 2^463 |
| F412 | 21,383 (< 2^15) | 412,597,277,036,535,862,786 | 69 | < 2^193 |

The initial runElemFast prefixes, including their entry paths, cost exactly 164,386 (F424) and 145,982 (F412) according to the source-derived replay in ../agent38-symrun-prefix-cost/README.md. The terminal step_DL_zero_halt transition is part of the final stepSym transition and is covered by the per-transition bound above.

Conditional on the per-transition cost lemma and kernel-checked trace maxima, the complete primitive halting times would therefore satisfy:

- F424: T < 2^463 + 2^18 < 2^464 < 2^512;
- F412: T < 2^193 + 2^18 < 2^194 < 2^256.

The repository's external champion baseline is S(6) > 2↑↑↑5, which is much larger than 2^512. Thus these two halting machines would be discharged as strictly below the champion, without needing their exact decimal halting times. This comparison is conditional, not a certified classification.

## Formalization route

The upstream BusyBeaver/Basic.lean API has multiStep_trans. Define

    def ReachWithin (M : Machine Γ Λ) (c c' : Cfg Γ Λ) (B : Nat) : Prop :=
      ∃ n, n ≤ B ∧ multiStep M c n = some c'

and prove additive composition directly with multiStep_trans:

    theorem ReachWithin.trans
        (h1 : ReachWithin M c1 c2 B1)
        (h2 : ReachWithin M c2 c3 B2) :
        ReachWithin M c1 c3 (B1 + B2) := by
      rcases h1 with ⟨n, hn, hstep⟩
      rcases h2 with ⟨m, hm, hstep'⟩
      refine ⟨n + m, Nat.add_le_add hn hm, ?_⟩
      exact multiStep_trans hstep hstep'

Then add a cost-indexed parallel to the existing stepPure_sound, sweepBB_sound, sweepCB_sound, tryRuleA_sound, tryRuleB_sound, and tryRuleBC_sound proofs. Do not try to extract a Nat from their existing ReflTransGen proofs in Prop.

Two independent obligations remain:

1. Prove the source-structural 2^40 M^2 per-stepSym cost lemma.
2. Kernel-check the maximum-field bounds over every intermediate state, not merely the checkpoint endpoints. The replay already computes the exact maxima; a Lean fold over each 4096-step chunk can certify the bound using the same deterministic transition function.

The source modules currently live only in the pinned upstream Cryptids tree (Lean 4.35.0-rc4), while the local BB6 project uses Lean 4.36.0-rc2 and does not contain HaltShared.lean. The local shell preflight in this invocation failed with a tool-level ClientError, so no CI compile was attempted. Until the exact dependency closure is available and the cost lemma and range fold compile, this remains an intermediate candidate rather than a publishable result.
