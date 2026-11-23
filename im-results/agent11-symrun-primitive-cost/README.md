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

Let `stepPure` be the exact source transition; let `stateA0`, `stateA`, `stateB`, and `stateC` be the literal source definitions in HaltShared.lean. Write `cost_N(s)` for the primitive cost along the **specific** `N` source `stepPure` witnesses, with zero-cost representation-only changes allowed. The source's `ruleA0_sound`, `ruleA_step_eq`, `ruleC_step_eq`, and four `ruleB_step_{AA,AB,BA,BB}` certificates fix the lengths as **46, 66, 46, 126/118/106/98**. Counting primitive costs of the underlying original-machine `execute n` rules produces the following affine formulas, currently checked by symbolic-shaped concrete replay over positive and boundary parameters:

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

## Reproduction and acceptance boundary

- [`symrun_cost_replay.cjs`](symrun_cost_replay.cjs) is an executable, instrumented clone of the independent [Agent38 checkpoint replay](../agent38-symrun-state-replay/symrun_state_replay.cjs). It still independently checks every literal upstream symbolic checkpoint and now reports `primitiveStepSymCost`, its category breakdown, and success counts. Invoke it through the same `run(fetchText)` interface, for example with Node's `fetch` function at the pinned source URLs.
- [`pure_cost_factory.cjs`](pure_cost_factory.cjs) is an independent instrumentation of one source `stepPure` transition and of the source `stateA0/stateA/stateB/stateC` constructors. It validates the exact fixed-block affine formulas for concrete natural-number parameters; the large unbounded macros are summed algebraically, not replayed.
- [`cost_wrapper_fragment.js`](cost_wrapper_fragment.js) records the separate instrumentation used by the full replay.
- Initial primitive prefix costs are independently recorded in [Agent38's prefix work](../agent38-symrun-prefix-cost/README.md). They have *not* been recertified here.

**Gap to promotion:** prove the seven affine fixed-block formulas for **all** natural parameters from the pinned original source, not just examples, and compose them into source-level costed Rule A/B/C and `stepSym` theorems in Lean. Then kernel-check the traced primitive-count fold, including the prefix, and audit the exact original-source import closure. The present numbers are high-quality **computational candidates**, not established mathematical proofs. No change should be made to `results/` or the global BB(6) upper-bound ledger before those obligations close.
