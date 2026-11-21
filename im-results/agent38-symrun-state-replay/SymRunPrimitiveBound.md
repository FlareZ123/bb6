# Coarse primitive-time bound candidate for SymRun F424/F412

**Status: conditional proof sketch; not yet a theorem.** This note turns the checkpointed state replay and source-derived rule costs into a deliberately loose primitive-time bound. It is intended to be challenged and then formalized with a cost-indexed reachability relation. Do not treat either machine as a certified `DecidedBelow` leaf yet.

Pinned source: `google-deepmind/cryptids` commit `3647718b5df22e1a61462dec0376bd204526285a`, using `BusyBeaver/Calculi/HaltShared.lean` and the F424/F412 machine modules.

## Exact primitive costs exposed by the source

Write (b_0) for the `step_BB_run0` cost, (b_1=3) for `step_BB_run1`, and (c_1) for the `step_CB_run0_run_pos` cost at parameter (d_2=0).

| Rule cost | F424 | F412 |
|---|---:|---:|
| (b_0) | 8 | 6 |
| (b_1) | 3 | 3 |
| `step_CB_run0_run_pos(0)` = (c_1) | 21 | 19 |
| `step_CB_run1` | 3 | 3 |
| variable `step_DL_run2(d)` | (3d+22) | (3d+20) |
| variable `step_CB_run0_run_pos(d)` | (3d+21) | (3d+19) |
| all other atomic cases | at most 9 | at most 9 |

The six repeated-block sweep lemmas in `HaltShared.lean` therefore have these exact costs:

| Sweep lemma | F424 | F412 |
|---|---:|---:|
| `sweep_BB_B1(k)` | (11k) | (9k) |
| `sweep_BB_C2(p)` | (14p) | (12p) |
| `sweep_BB_C12(m)` | (25m) | (21m) |
| `sweep_CB_B1(k)` | (21k) | (19k) |
| `sweep_CB_B2(p)` | (24p) | (22p) |
| `sweep_CB_B12R(m)` | (45m) | (41m) |

For example, `sweep_BB_C12` composes `step_BB_r1_r0_r1_comm` (cost (b_0+2b_1)) with `step_BB_r0_r1` (cost (b_0+b_1)), giving (2b_0+3b_1). The largest coefficient across both machines and all six sweeps is 45.

Let (Mge1) bound every run value and repeat counter in a symbolic state. Each `stepPure` case either:
- uses at most one of the six repeated-block sweeps, with counter at most (M); or
- uses one atomic primitive rule, whose cost is at most (3M+22) (the remaining atomic costs are at most 9).

Thus the source proof decomposition gives the simple bound

[
  C_{mathrm{stepPure}} le max(45M,3M+22,9)
  le 50(M+1).
]

This is the key local estimate. It is independent of the number of tokens because one `stepPure` transition selects at most one sweep lemma.

## Cost of one `stepSym` transition

The proof of `stepSym_sound` factors through `sweepBB`, `sweepCB`, `stepElemThenBB`, and one of `tryRuleA`, `tryRuleB`, `tryRuleBC`.

The checkpoint replay in [`symrun_state_replay.cjs`](symrun_state_replay.cjs) gives the following maximum *outer-state* symbolic-token count:

- F424: 94;
- F412: 78.

Use the common bound (Lle94). Each `sweepBB` or `sweepCB` recursion consumes one token from its scanned side. A token contributes at most one repeated-block sweep of cost (45M), or one atomic case of cost at most 24. A `stepElemThenBB` fallback adds one atomic transition and scans at most three additional left tokens. Consequently, the combined outer `sweepBB/sweepCB/stepElemThenBB` work is below (2^{14}M).

For the three successful rule macros, the source soundness lemmas use:

- Rule A: 46 `stepPure` calls for `ruleA0`, then 66 per iteration of `ruleA_iter`. The iteration count is (m_{m new}le M), so at most (46+66Mle112M) calls.
- Rule B: one of 98, 106, 118, or 126 `stepPure` calls per `ruleB_iter) iteration. The iteration count (n_3le M), so at most (126M) calls.
- Rule C: 46 `stepPure` calls per `ruleC_iter) iteration. The iteration count (n_4le M), so at most (46M) calls.

Hence every successful macro uses at most (126M) `stepPure` calls.

The affine parameter updates in the three iterator theorems give a conservative (8M) bound on every counter inside those `stepPure` sequences:
- Rule A's boundary values are bounded by the original (M); its micro-sequence has at most 66 steps.
- Rule B increases its (p)-parameter by 2 and its (d_2)-parameter by 4 per macro iteration, with (n_3le M); the largest boundary field is at most (5M+33), before at most 126 unit-sized micro-updates.
- Rule C increases (k) and (d_2) by 2 per macro iteration, with (n_4le M); the largest boundary field is at most (3M), before at most 46 unit-sized micro-updates.

For the actual traces (M) is vastly larger than 128, so these are all below (8M). Therefore each internal `stepPure` costs at most (50(8M+1)le450M), and the successful rule macros cost at most

[
  126Mcdot450M=56{,}700M^2 < 2^{16}M^2.
]

Adding the outer sweep/fallback work gives the conservative per-transition candidate

[
  oxed{C_{mathrm{stepSym}}(s)le 2^{20}M(s)^2.}
]

The constant (2^{20}) is deliberately loose. The inequality is a proof target based on the displayed source inductions, not yet a Lean theorem. In particular, the unit-change bound for the micro-sequences and the outer sweep accounting should be made explicit in a formal cost semantics.

## Concrete trace maxima and resulting candidate bounds

The independent replay matches every literal upstream checkpoint and reaches the final `.HALT` state:

| Machine | `stepSym` calls | Maximum field (M) | Bit length | Bound from (2^{20}M^2) per call |
|---|---:|---:|---:|---:|
| F424 | 70,511 (<2^{17}) | 12,464,561,897,144,001,482,331,935,594,779,263,804,489,570,179,353,031,112,091,137 | 203 | (<2^{443}) |
| F412 | 21,383 (<2^{15}) | 412,597,277,036,535,862,786 | 69 | (<2^{173}) |

The initial `runElemFast` prefixes, including their entry paths, cost exactly 164,386 (F424) and 145,982 (F412) according to the source-derived replay in [the prefix-cost dossier](../agent38-symrun-prefix-cost/README.md). The terminal `step_DL_zero_halt` transition is part of the final `stepSym` transition and is covered by the per-transition bound above.

Conditional on the per-transition cost lemma and kernel-checked trace maxima, the complete primitive halting times would therefore satisfy:

- F424: (T<2^{443}+2^{18}<2^{444}<2^{512});
- F412: (T<2^{173}+2^{18}<2^{174}<2^{256}).

The repository's external champion baseline is (S(6)>2\uparrow\uparrow\uparrow5), which is much larger than (2^{512}). Thus these two halting machines would be discharged as strictly below the champion, without needing their exact decimal halting times. This comparison is conditional, not a certified classification.

## Formalization route

The upstream `BusyBeaver/Basic.lean` API has `multiStep_trans`. Define

```lean
def ReachWithin (M : Machine Γ Λ) (c c' : Cfg Γ Λ) (B : Nat) : Prop :=
  ∃ n, n ≤ B ∧ multiStep M c n = some c'
```

and prove additive composition directly with `multiStep_trans`. Then add a cost-indexed parallel to the existing `stepPure_sound`, `sweepBB_sound`, `sweepCB_sound`, `tryRuleA_sound`, `tryRuleB_sound`, and `tryRuleBC_sound` proofs. Do not try to extract a Nat from their existing `ReflTransGen` proofs in `Prop`.

Two independent obligations remain:

1. Prove the source-structural (2^{20}M^2) per-`stepSym` cost lemma.
2. Kernel-check the maximum-field bounds over every intermediate state, not merely the checkpoint endpoints. The replay already computes the exact maxima; a Lean fold over each 4096-step chunk can certify the bound using the same deterministic transition function.

The source modules currently live only in the pinned upstream Cryptids tree (Lean 4.35.0-rc4), while the local BB6 project uses Lean 4.36.0-rc2 and does not contain `HaltShared.lean`. This note does not bypass that compatibility/preflight requirement. Until the exact dependency closure is available and the cost lemma and range fold compile, this remains an intermediate candidate rather than a publishable result.
