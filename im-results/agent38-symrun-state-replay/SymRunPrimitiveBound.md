# Boundary-safe primitive-time bound for SymRun F424/F412

**Status: conditional proof sketch, not yet a theorem.** This note replaces the earlier derivation that assumed the outer maximum field (M\ge376). That premise is false at both authentic initial symbolic states: F424 and F412 each start at `initSymCyc3` with maximum field `M=2` (F424 has a `.run 2` token and F412 has `.run 2` as its maximum). The replacement below works for every (M\ge0) and sharpens the conditional complete bounds by one bit, to F424 (T<2^{463}) and F412 (T<2^{193}).

Pinned source: `google-deepmind/cryptids` commit `3647718b5df22e1a61462dec0376bd204526285a`, using `BusyBeaver/Calculi/HaltShared.lean` and the two F424/F412 machine modules.

## Source primitive costs

The two machines differ only in the two variable-cost rules and the BB-run0 / exit costs.

| Rule cost | F424 | F412 |
|---|---:|---:|
| `step_BB_run0` | 8 | 6 |
| `step_BB_run1` | 3 | 3 |
| `step_BB_run2` | 5 | 5 |
| `step_BB_run3`, `step_BB_run_ge4` | 9 | 9 |
| `step_DL_run2(d)` | (3d+22) | (3d+20) |
| `step_CB_run0_run_pos(d)` | (3d+21) | (3d+19) |
| `step_CB_run0_run0` | 6 | 6 |
| `step_CB_run1` | 3 | 3 |
| other atomic cases | at most 9 | at most 9 |

The variable costs follow directly from the upstream proofs:
- `step_DL_run2(d)`: 6 initial steps, then `cyc_R_A(d+1)` at 3 steps per cycle, then `exit_R_A` at 13 / 11 steps.
- `step_CB_run0_run_pos(d)`: 5 initial steps, then `cyc_R_A(d+1)`, then the same exit.

The six repeated-block sweep coefficients are:

| Sweep lemma | F424 | F412 |
|---|---:|---:|
| `sweep_BB_B1(k)` | (11k) | (9k) |
| `sweep_BB_C2(p)` | (14p) | (12p) |
| `sweep_BB_C12(m)` | (25m) | (21m) |
| `sweep_CB_B1(k)` | (21k) | (19k) |
| `sweep_CB_B2(p)` | (24p) | (22p) |
| `sweep_CB_B12R(m)` | (45m) | (41m) |

Thus every repeated-block sweep costs at most (45x) when its repeat parameter is (x). Every non-variable atomic branch costs at most 9, and either variable atomic branch costs at most (3x+22).

## State measures and finite trace obligations

For a symbolic state (s=(mode,L,R)), let:
- (M(s)) be the maximum numeric field among all `.item (.run n)`, `.repB1 n`, `.rep2 n`, and `.rep12 n` tokens in (L,R);
- (T(s)=|L|+|R|).

The independent replay matches every literal upstream checkpoint (F424 18/18; F412 6/6). It records the following maxima over **every intermediate state**, not just checkpoint endpoints:

| Metric | F424 | F412 |
|---|---:|---:|
| `stepSym` transitions | 70,511 | 21,383 |
| maximum numeric field | 203 bits | 69 bits |
| maximum symbolic-token count (T) | 94 | 78 |

The draft exact-source range folds for both (M) and (T) are now in `im-results/agent42-cryptids-upstream-191-overlap/SymRunTraceStats.lean`; they still need an exact Lean 4.36.0-rc2 import-closure compile. The empirical maxima alone are not a theorem.

## Boundary-safe per-transition estimate

Assume (T(s)\le94), and write (M=M(s)). No lower bound on (M) is assumed.

### 1. One `stepPure` transition

A complete constructor-by-constructor source audit confirms the first fact:

1. (M(stepPure(s))\le M(s)+1). In `bumpSymL/R`, an ordinary run can rise only from (d) to (d+1). Positive `repB1` cases decrease their counter and emit only run-0/run-1 tokens. Positive `rep2` and `rep12` cases decrease their counters; `bumpSymL` may emit a run-2 token, but this exceeds the old maximum only when the old repeat counter is exactly 1, hence by exactly one. Zero-repeat heads recurse and `peelPureTok` only lowers repeat counters while exposing run-0/run-1 literals. In `stepPureCB`, the only explicit increases are the single `k+1` and `p+1) branches. The branch that calls both `bumpSymL` and `bumpSymR` still raises each affected field by at most one, so their maximum does not accumulate two increments. All other branches rearrange tokens or prepend zeros.
2. The primitive cost of one `stepPure` transition at a state with maximum field (X) is at most
   [
   \max(45X,\;3X+22,\;9)\le50(X+1).
   ]
   A BB repeated-token branch invokes at most one of the six repeated-block sweeps; every other branch invokes at most one atomic rule.

The field-growth proof can be split into three list lemmas:
- `max(bumpSymL(xs)) ≤ max(xs)+1`;
- `max(bumpSymR(xs)) ≤ max(xs)+1`;
- `max(peelPureTok(t,xs)) ≤ max(t::xs)`.

Then inspect the four `stepPure` modes. BB uses at most one `bumpSymR` after optional non-increasing peeling; DL uses non-increasing peeling followed by one `stepElemDL`; CB uses at most one `bumpSymL`, except the two explicit repeat-counter branches, which increment exactly one counter by one; HALT is unchanged. The soundness cases `stepPureBB_sound`, `stepPureDL_sound`, and `stepPureCB_sound` (HaltShared lines 3780–3906) likewise use at most one repeated-block sweep or one atomic rule per branch.

The field-growth statement now has `stepPure_field_growth` and an n-step corollary in `SymRunTraceStats.lean`. Agent 44 reports a successful Lean 4.36.0-rc2 source-equivalent compile with axiom profiles `[propext, Quot.sound]`; exact imported-source compilation remains pending. The primitive-cost bound per `stepPure` transition is still not Lean-certified.

### 2. The outer CB sweep

The source `sweepCB` scans at most (T\le94) right-side tokens. Each scanned repeat token can trigger one `eatFuel` call with fuel 4. A fuel step that merges an existing repeat counter conserves the total counter sum; a fuel step that matches a literal block increases that sum by one. Thus each call increases the total repeat-counter sum by at most four. The initial sum of repeat counters is at most (94M), so after the sweep every repeat counter is bounded by
[
94M+4\cdot94=94M+376\le512(M+1).
]
The `bumpSymL` calls can increase a run field by at most one each; there are at most 94 calls, so every field after the sweep is also bounded by (M+94\le95(M+1)\le512(M+1)).

The list-length bound can be sharpened. First, (|bumpSymL(L)|\le |L|+5): the largest expansion replaces one `.rep12 (m+1)` token by six tokens, and all zero-repeat recursion only removes tokens. In the `run0/run1` and `run1` sweep branches, the prepended run-zero tokens replace exactly the right tokens consumed; the only net growth is the at-most-five-token increase from `bumpSymL`. A repeat branch moves one right repeat token to the left, while `eatFuel` replaces it by one repeat token or contracts the left list. There is at most one `bumpSymL` call per consumed right token. Hence
[
T(\operatorname{sweepCB}(L,R))\le T(L,R)+5|R|\le6T\le564.
]

For primitive time, each scanned right token contributes at most one repeated-block sweep of coefficient at most 45 with parameter at most `M`, or one atomic rule of cost at most `3M+22`. Therefore the complete `sweepCB` cost is below `94·(45M+25(M+1))<2^13(M+1).

### 3. Fallback path

If `afterSweepCB` does not recognize Rule A/B/C, it performs one `stepElemThenBB`. Among the `stepElemCB` branches that actually return BB, the net total-token increase is at most six: `bumpSymL` contributes at most five, and the `run2` / `run(d+3)` cases replace one right token by two. The `run0` BB cases are no worse. The branch that prepends a parameter-sized zero prefix returns CB, so it does not invoke `sweepBB`. Thus the fallback `sweepBB` scans at most (564+6=570) tokens. The earlier eight-token statement is a safe gross-insertion bound, but six is the net list-length bound needed here.

Every repeat parameter read from the remaining left list is at most (512(M+1)). A single scanned token therefore costs at most
[
45\cdot512(M+1)+25(M+1)=23{,}065(M+1).
]
Across at most 570 tokens this is (13{,}147{,}050(M+1)<2^{24}(M+1)). The preceding atomic transition and the outer CB sweep together keep all non-macro work below
[
2^{25}(M+1),
]
since the outer sweep is below (2^{13}(M+1)) and the fallback atomic cost is at most (25(M+1)). The direct BB-mode path is smaller (at most 94 scanned tokens). In DL mode, `peelL` expands at most one head token by five tokens; its only BB-producing branch therefore leaves at most 99 tokens for `sweepBB`. The branch that prepends a parameter-sized zero prefix remains in CB mode.

### 4. Rule A/B/C macro path

After `sweepCB`, at most one of the Rule A/B/C macros is attempted.

- Rule A uses (46+66n_A) `stepPure` calls, with (n_A\le M), hence fewer than (2^7(M+1)).
- Rule B uses at most (126n_B) calls, with (n_B\le512(M+1)), hence at most (64{,}512(M+1)<2^{16}(M+1)).
- Rule C uses at most (46n_C) calls, with (n_C\le512(M+1)), hence fewer than (2^{15}(M+1)).

Thus every recognized macro uses fewer than (2^{16}(M+1)) `stepPure` calls. Its initial maximum field is at most (512(M+1)). By the one-step growth fact above, every intermediate field during the macro is bounded by
[
512(M+1)+64{,}512(M+1)=65{,}024(M+1)<2^{16}(M+1).
]
Consequently each `stepPure` call costs less than (2^{22}(M+1)), and the entire macro costs less than
[
2^{16}(M+1)\cdot2^{22}(M+1)=2^{38}(M+1)^2.
]

Combining the macro and fallback cases, every `stepSym` transition on a state with (T\le94) satisfies the boundary-safe estimate
[
\boxed{C_{stepSym}(s)<2^{39}(M(s)+1)^2.}
]
This proof sketch does not require (M\ge376).

## Consequences if the range folds and source cost semantics are certified

The complete-trace maxima imply:
- F424: (M+1\le2^{203}), (70{,}511<2^{17}), so the `stepSym` phase costs less than (2^{39+406+17}=2^{462}).
- F412: (M+1\le2^{69}), (21{,}383<2^{15}), so the `stepSym` phase costs less than (2^{39+138+15}=2^{192}).

The initial `runElemFast` prefixes have 19,217 / 19,255 `stepElemM` iterations. The existing Lean transcription in `im-results/agent42-symrun-prefix-growth/{PrefixGrowth,PrefixCostTable}.lean` proves the max-run growth and the coarse prefix arithmetic below (2^{31}); the original-source costed `stepElemM` transfer is still required. The source halting proof also applies the separate `step_DL_zero_halt` transition (+1) after the final abstract HALT checkpoint.

Conditional complete primitive-step bounds are therefore:
- F424: (steps<2^{462}+2^{31}+1<2^{463}).
- F412: (steps<2^{192}+2^{31}+1<2^{193}).

Both are far below (2^{512}), and hence below the published (S(6)>2\uparrow\!\uparrow\!\uparrow5) champion baseline under the standard Knuth-arrow convention. This would classify the two exact rooted machines as non-champions, not solve BB(6).

## Required formal acceptance

1. Extend the exact `ReachesIn` pilot in `im-results/agent42-cryptids-upstream-191-overlap/SymRunCostedStepPilot.lean` to all machine-specific atomic `execute n` rules and the six repeated-block sweep lemmas; the current uncompiled pilot covers the cycle, exit, BB-run0, and two variable-cost rules for F424.
2. Compile and audit the included `stepPure_field_growth` / n-step theorem against exact imports; separately prove the (50(X+1)) primitive-cost bound for each `stepPure` branch.
3. Prove the `sweepCB` counter-sum and token-count bounds, then the fallback `sweepBB` bound.
4. Prove the Rule A/B/C call-count bounds and compose them into the (2^{39}(M+1)^2) transition theorem.
5. Kernel-check both maximum-field and token-count folds over every intermediate state in every checkpoint chunk.
6. Certify the initial `runElemFast` prefix cost from the original `execute` rules, include the separate final +1, and transfer through `multiStep_toBB` and the local exact halting adapter.
7. Compile the exact import closure under Lean 4.36.0-rc2 and audit all exported axiom profiles. No CI dispatch should substitute for the required local preflight.

## Pinned source anchors

- SymRun definitions: `HaltShared.lean` 2346-3014.
- `HasSymRunRules` machine-specific rule interface: 2473-2520.
- `sweepCB`, `sweepBB`, `tryRuleA/B/C`, and `stepSym`: 2861-3014.
- Repeated-block sweep proofs: 3281-3405.
- `stepElemBB/DL/CB` soundness: 3460-3574.
- `sweepBB_sound` / `sweepCB_sound`: 3576-3718.
- `stepPure` and its soundness: 3750-3915.
- Rule A/C/B iterators: 3984-4239.
- `tryRuleB_sound`, `tryRuleBC_sound`, `afterSweepCB_sound`, `stepSym_sound`: 4268-4432.
- Exact initial and terminal `execute` costs: the F424/F412 machine files, lines 69-265.


## 2026-11-21 addendum: numeric-sum fallback bound and outer-sweep audit

Agent 44 has since formalized the numeric-field-sum chain in `SymRunTraceStats.lean`: `sweepCB_num_sum_le_94M282`, `sweepCB_stateFieldMax_le_94M282`, and (on the BB-producing fallback branch) `cb_fallback_bb_input_field_max_le_94M285`. The last theorem gives a direct maximum-field bound at the input to the fallback BB sweep, stronger and simpler than the earlier separate counter-sum and bump-count bounds.

Using that bound and the exact F424 BB costs (11/14/25 per repeat unit; at most 9 for an atomic BB item branch), the ≤570-token fallback BB sweep has cost at most
`570 * (25 * (94M + 285) + 9) = 1,339,500M + 4,066,380 < 2^22(M+1)`.
This sharper coefficient-25 bound is currently an arithmetic derivation, not yet a Lean theorem; the generic costed `sweepBB_within` pilot remains at coefficient 50. With the outer CB sweep (<2^13(M+1)) and fallback `stepElemCB` (≤25(M+1)), the non-macro path is <2^23(M+1).

A separate source-level review found no induction, endpoint-encoding, or product-budget defect in the current `sweepBB_within` / `sweepCB_within` pilot proofs. One costed Rule A gap remains: upstream `ruleA0_sound` contains a 46-`stepPure` prelude from `stateA0` to `stateA 0`; the pilot has costed `ruleA_step` and `ruleA_iter` but not this initial 46-step segment. Full `afterSweepCB` / `stepSym` dispatch composition is also not yet present.
