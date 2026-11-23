# Candidate exact primitive halting times for Cryptids F424 and F412

**Agent 11, 23 November 2026. Status: reproducible, source-shaped computational research; not yet a formal theorem.** The upstream Cryptids halting certificates establish that both machines halt, but only macro-step counts were available in this repository. This dossier assigns the primitive costs of the actual machine rules to every accelerated step, including a closed-form sum over each unbounded A/B/C macro loop. It produces **candidate exact** blank-tape primitive halting times, rather than just conditional upper bounds.

Pinned source: `google-deepmind/cryptids`, commit `3647718b5df22e1a61462dec0376bd204526285a`, `BusyBeaver/Calculi/HaltShared.lean` and the two `BusyBeaver/BB6/Halt/` machine files.

## Computed outcomes

| Exact source machine | Initial RLE-prefix steps | stepSym iterations | Candidate stepSym primitive steps | Candidate complete primitive steps |
| --- | ---: | ---: | ---: | ---: |
| F424 `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH` | 164,386 | 70,511 | 9562364499971251651655073023782161847733149952836448655080514749023620422714072692983157652446098323400883787472183908315943 | **9562364499971251651655073023782161847733149952836448655080514749023620422714072692983157652446098323400883787472183908480330** |
| F412 `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA` | 145,982 | 21,383 | 9217091204829760959746640857348768637436799 | **9217091204829760959746640857348768637582782** |

The complete totals add the independent initial RLE-prefix costs from [Agent38's prefix replay](../agent38-symrun-prefix-cost/README.md) plus the separate final `step_DL_zero_halt` primitive step. The totals occupy only **412 bits** (F424) and **143 bits** (F412); these are numerically far below the published BB(6) lower bound, if their exact costs can be certified. They **do not** determine BB(6) and are not yet accepted classifications.

For F424 the stepSym stage's charged sums, grouped by source proof family, are: atomic **483964**, ordinary repeated sweeps **30616787764897741996863904134148576631779983341047149648027884127**, Rule A **2426658070398894036164691645493654998883151400023485616144537320386315643327455923402178645575077924548755308914762285853374**, Rule B **2030846464403952478436609319170757003638491034470874395218653431522304189748534488014320569097000618718999531217862882291820**, and Rule C **5104859965168405137053772059117749845211507518342088643717293380327235691896085417662524289197388000149787900189910711802658**. F424 uses A/B/C success counts **473/472/472**. F412 uses **149/148/148**. All 18 F424 and six F412 exact symbolic source checkpoints still match unchanged.

## Fixed-block exact-cost candidates

Let `stepPure` be the exact source transition; let `stateA0`, `stateA`, `stateB`, and `stateC` be the literal source definitions in HaltShared.lean. Write `cost_N(s)` for the primitive cost along the **specific** `N` source `stepPure` witnesses, with zero-cost representation-only changes allowed. The source's `ruleA0_sound`, `ruleA_step_eq`, `ruleC_step_eq`, and four `ruleB_step_{AA,AB,BA,BB}` certificates fix the lengths as **46, 66, 46, 126/118/106/98**. Counting primitive costs of the underlying original-machine `execute n` rules produces the following affine formulas. **All fourteen formula families are checked for arbitrary nonnegative integer parameters**, not merely for sampled inputs, by the source-shaped affine abstract interpreter described below. The checker remains an independently written computational model, not a Lean proof:

| Fixed source block, with input parameters | F424 cost | F412 cost |
| --- | ---: | ---: |
| `46 × stepPure` from `stateA0(k+1,d+6)` | `32k + 314` | `28k + 284` |
| `66 × stepPure` from `stateA(m,k+1,d+6)` | `140m + 32k + 454` | `124m + 28k + 408` |
| `46 × stepPure` from `stateC(p+3,k+1,d)` | `76p + 64k + 486` | `68p + 56k + 434` |
| Rule B from `stateB(sepA,sepA,p+1,m+2,k+1,d)` (126) | `152p + 140m + 32k + 1048` | `136p + 124m + 28k + 942` |
| Rule B, separators A/B (118) | `152p + 140m + 32k + 978` | `136p + 124m + 28k + 880` |
| Rule B, separators B/A (106) | `152p + 140m + 32k + 896` | `136p + 124m + 28k + 806` |
| Rule B, separators B/B (98) | `152p + 140m + 32k + 826` | `136p + 124m + 28k + 744` |

(The `stateA0` row uses input `k+1`, so the base cost is `32k+314`, not `32(k+1)+314`.)

The repeat-count `m` never needs expansion in runtime: the `stepPure` witness cost is affine. The coefficients are not inferred from macro step counts; they count machine-specific atomic transitions and repeated-block sweep costs. In particular, the F424 and F412 coefficients differ because `step_BB_run0`, `exit_R_A`, and the repeated-block sweeps have different primitive costs.

## Closed macro-cost candidate formulas

Using only the fixed block formulas above and the **exact upstream induction decomposition**:

- **A success:** source `tryRuleA` with right `run d`, `n=⌊d/6⌋≥2`, and ending `repB1 K` with `K≥n`. One 46-step initial block and `n−1` 66-step blocks sum to
  [
  A_{424}=n(32K+54n+228),\quad A_{412}=n(28K+48n+208).
  ]
- **C success:** source `tryRuleBC` with leading `rep2 P`, ending `repB1 K`, and `n=P−2≥1`. Its `n` 46-step blocks sum to
  [
  C_{424}=n(102n+64K+320),\quad C_{412}=n(90n+56K+288).
  ]
- **B success:** source `afterSplitB2` with `P≥2` explicitly counted `011` blocks, `rep12(n+1)`, and ending `repB1 K` with `K≥n+1`. Its `n` fixed blocks sum to
  [
  B_{424}=n(206n+152P+32K+c_{424}),\quad
  B_{412}=n(184n+136P+28K+c_{412}),
  ]
  with separator pairs `AA/AB/BA/BB` giving `c424=506/436/354/284` and `c412=458/396/322/260`.

All these closed forms are quadratic in the unbounded macro iteration count. The outer sweeps and fallback atomic steps are charged directly from the original per-branch `ReachesIn` costs, with no unbounded replay of the expanded tape.


## Exact-cost potentials: a telescoping proof of all unbounded macro sums

The fixed-block costs have a stronger structure than merely being affine: **they are discrete gradients of quadratic integer-valued potentials.** Writing \(m,k,p\) for the literal source-state counters, define:

| Variant | A potential \(\Phi_A(m,k)\) | C potential \(\Phi_C(p,k)\) |
|---|---|---|
| F424 | \(-70m^2+16k^2+368k\) | \(38p^2-16k^2+168p\) |
| F412 | \(-62m^2+14k^2+332k\) | \(34p^2-14k^2+152p\) |

For the B rule with macro separator-pair offset \(c\) (F424 \(506,436,354,284\); F412 \(458,396,322,260\)), define

\[
\Phi_{B,424,c}(p,m,k)=-38p^2+70m^2+16k^2+(c+12)m,
\]
\[
\Phi_{B,412,c}(p,m,k)=-34p^2+62m^2+14k^2+(c+12)m.
\]

Each fixed-block cost is an **exact potential drop** on its source-prescribed counter change. For example,

\[
\Phi_{A,424}(m,k+1)-\Phi_{A,424}(m+1,k)=140m+32k+454
\]
and
\[
\Phi_{B,424,c}(p+1,m+2,k+1)-\Phi_{B,424,c}(p+3,m+1,k)=152p+140m+32k+c+542.
\]

The analogous C drop is \(76p+64k+486\) on \((p+3,k+1)\to(p+2,k+3)\). Therefore along **any** successful sequence of A/B/C source induction steps, the cost telescopes to the difference between just its *initial and final* potential values. This directly yields all six quadratic macro costs from their root counters—no unbounded summation or approximate bound is needed.

- [`MacroCostPotential.lean`](MacroCostPotential.lean) states and proves twelve algebraic theorems (both variants × three fixed-block potential drops and three closed macro endpoint formulas) using `ring` over integers.
- [`MacroCostArithmetic.lean`](MacroCostArithmetic.lean) independently states and proves the twelve natural-number recurrence/summation identities underlying the same macro formulas.
- The symbolic affine block checker supplies the still-to-be-source-linked *premises* that these are the primitive costs of the 46–126 original `stepPure` rules. Thus the integer potential identities are unconditional arithmetic statements, while their use as exact Turing-machine step counts remains conditional on the source connection.

This potential approach is preferable to repeatedly simulating huge macro iterations and is reusable for any accelerated system whose block costs are affine in counters that evolve by translations.


## Auditable finite certificate structure

A valid all-parameter block cost proof is reducible to a finite straight-line trace: for each of the 14 machine–block pairs, the symbolic evaluator performs 46–126 source-shaped `stepPure` transitions, maintains an affine cost in the free variables (p,m,k,d), and checks every branch guard against the **whole** natural orthant. Each successful run returns a coefficient vector `[constant,p,m,k,d]`, with zero dependence on `d` and no inspection of a symbolic unrestricted `R_tail`. Those coefficient vectors are shown in the table above. The affine-guard argument uses componentwise coefficient signs and exact zero tests, so there is no unsound appeal to testing a few concrete inputs.

The source's exact `execute n` rules give machine-specific primitive costs, including `step_DL_run2(d) = 3d+22/20` and `step_CB_run0_run_pos(d) = 3d+21/19`, while the six repeated-block transfer lemmas carry the coefficients 11/9, 14/12, 25/21, 21/19, 24/22, 45/41. The finite checker requires no arithmetic larger than linear forms to establish the fixed-block costs. Quadratic macro forms arise only from summing these *proven-symbolically-relative-to-source* affine forms under the previously certified inductive macro decomposition.

**Boundary:** the source-shaped evaluator itself is trusted JavaScript; no theorem about its interpretation of the upstream Lean source has yet been typechecked in Lean. The 24 finite checkpoints in `checkpoint_costs.json` are replayed and tested against source states, not kernel-checked for their associated costs. Thus even though the abstract interpretation ranges over all nonnegative parameter values, the resulting complete primitive times are **candidate exact values** pending the model-to-source and count-fold proof obligations.

**Source-linked proof progress (23 November 2026):** [run 45119191819](https://github.com/FlareZ123/bb6/actions/runs/45119191819) successfully compiled `SourceCostModel.lean` and `SourceCostCombinators.lean` over the **actual upstream** `BusyBeaver.SymRunEngine.stepPure` transition, using Lean 4.36.0-rc2. The verified `costIter_add`, `costIter_exact_reaches`, and `costIter_exact_checkpoint` theorems establish exact primitive-count trace composition **conditional on** the original-machine one-step premise `ExactSymStep M is424`. This does not yet provide an unconditional F424/F412 halting-time theorem.

**Exact original-machine primitive-witness status:** `SourceExactF424Core.lean` remains an intermediate draft. Focused raw-source diagnostics 45126155156, 45127528380, 45128248162, and 45129111607 all failed before acceptance; the latest completed run (45129111607) still reported unsynthesized intermediate configuration metavariables in repeated-step witnesses and a simp recursion loop in repeated-block endpoint normalization. The latest source edit is commit `8c2eeeb48a79cc9c9d29a8b1fa9db636ec2107d0`; it has **not** been compiled. Run 45129893355 was cancelled before compilation. No full `agent11-symrun-exact-bb.yml` gate has been dispatched. Agent 38 has separately repaired the BB `strictNat_eq` and CB case4 `costSweepCB` reductions in `SourceExactSweepBB424.lean`, but that file also remains uncompiled.

**Static branch-cost alignment:** The current Core draft contains 32 `ReachesIn` declarations. Their declared indices match the F424 `costPure` branches: BB `[]/zero/run0/run1/run2/run3/run≥4` = `1/1/8/3/5/9/9`; DL `run0/run1/run2(d)` = `1/3/(3d+22)`; CB `nil/zero/run1/run2/run≥3` = `2/2/3/5/5`; CB `run0` with right `nil/zero/run0/run(d+1)` = `3/3/6/(3d+21)`; repeated transfers = `11,14,25` (BB) and `21,24,45` (CB). This static declaration-level audit found no off-by-one mismatch between the draft witnesses and the cost table; it does **not** validate the uncompiled proofs.

**Source repair applied, not yet compiled (23 November 2026):** `SourceExactF424Core.lean` now defines `nextCfg c := (step target_tm c).getD default`, proves `step_eq_some_nextCfg` under an `isSome` premise, and rewrites `reachesIn_step_left_succ` so no unconstrained intermediate `c₂` metavariable is required. The `stepWithin` tactic now proves `isSome` and simplifies the computed successor. All six repeated-block endpoint normalizers no longer include `Nat.add_one`; they retain `repBlock_succ_right` and append associativity so the source rewrite can match `k+1`. Commit `5eded85b48cb7dd5e6bdaef8fc0d8440714e74d2`. This is a reasoned source-level repair, not Lean acceptance; exact compile remains pending.

The prescribed local Lean 4.36.0-rc2 preflight is blocked in the current environment: both `python.exec` and `container.exec` returned tool-level `ClientError` before executing a command. No local Lean executable or archive-size measurement was obtained. Do not dispatch further F424 CI until a working local RC2 preflight is available or the collective dependency-ordered SymRun gate is ready for one targeted run. Do not describe the exact witnesses as kernel-checked until the exact dependency closure passes with an acceptable axiom profile.

**Shared BB-sweep source repair:** the exact-source BB-sweep run `45147110361` was cancelled before the proof stage after inspection found two definite syntax errors in `im-results/agent44-symrun-field-growth/SymRunBBBase.lean`: the `.rep12 m` branch of `tokNumSum` lacked `=> m`, and the corresponding theorem branch had a stray `=> m` after `rfl`. Both clauses were corrected in commit `9b45b182cc91e3af8b1ae3caa55e70b6668bf3f5`, and Agent 44 was notified. This is only a syntax correction; the isolated BBBase/BBBounds closure is still unaccepted.

**Earlier Stats gate status:** run `45137136319` did compile `stepElemCB_BB_num_sum_le` against the pinned Cryptids source with axiom profile `[propext, Quot.sound]`, but the overall broad module audit still failed later. Do not treat the whole Stats module or downstream BB bounds as accepted.

**Lean CI confirmation (23 November 2026):** [workflow run 45117981961](https://github.com/FlareZ123/bb6/actions/runs/45117981961) **succeeded** under Lean 4.36.0-rc2. All twelve natural-number macro sum/recurrence identities in `MacroCostArithmetic.lean`, twelve specialized integer potential drops and macro endpoint identities, and two generic affine-translation potential lemmas in `MacroCostPotential.lean` were kernel-checked. `#print axioms` reported only the standard `propext` axiom for the natural-number recurrence theorems; no `sorryAx` or `native_decide` was used. **This success does not certify the source-to-machine primitive cost premises or the full candidate halting times.**

## Reproduction and acceptance boundary

- [`symrun_cost_replay.cjs`](symrun_cost_replay.cjs) is an executable, instrumented clone of the independent [Agent38 checkpoint replay](../agent38-symrun-state-replay/symrun_state_replay.cjs). It still independently checks every literal upstream symbolic checkpoint and now reports `primitiveStepSymCost`, its category breakdown, and success counts. Invoke it through the same `run(fetchText)` interface, for example with Node's `fetch` function at the pinned source URLs.
- [`pure_cost_factory.cjs`](pure_cost_factory.cjs) is an independent instrumentation of one source `stepPure` transition and of the source `stateA0/stateA/stateB/stateC` constructors. It validates the exact fixed-block affine formulas for concrete natural-number parameters; the large unbounded macros are summed algebraically, not replayed.
- [`affine_block_certificate.cjs`](affine_block_certificate.cjs) symbolically executes all fourteen fixed-length proof blocks over arbitrary nonnegative integer parameters p,m,k,d with an affine-expression domain. Every branch comparison must be uniformly true or uniformly false on the **entire** nonnegative parameter orthant; otherwise the checker throws. An opaque tail sentinel throws if the execution ever inspects the unconstrained `R_tail`. The 14 symbolic executions halt successfully and give exactly the coefficients in the table, independent of `d` and `R_tail` (no loop over parameter values). This is a machine-checkable universal certificate **relative to the handwritten translation** of the source transitions and cost table. A source-level Lean theorem remains necessary to establish equivalence to the original machine.
- [`checkpoint_costs.json`](checkpoint_costs.json) records the complete cumulative primitive cost and Rule A/B/C hit counts at all 18+6 original upstream symbolic checkpoints; this is the finite trace-fold certificate for the candidate full times.
- [`cost_wrapper_fragment.js`](cost_wrapper_fragment.js) records the separate instrumentation used by the full replay.
- Initial primitive prefix costs are independently recorded in [Agent38's prefix work](../agent38-symrun-prefix-cost/README.md). They have *not* been recertified here.

**Gap to promotion:** prove the seven affine fixed-block formulas for **all** natural parameters from the pinned original source, not just examples, and compose them into source-level costed Rule A/B/C and `stepSym` theorems in Lean. Then kernel-check the traced primitive-count fold, including the prefix, and audit the exact original-source import closure. The present numbers are high-quality **computational candidates**, not established mathematical proofs. No change should be made to `results/` or the global BB(6) upper-bound ledger before those obligations close.
