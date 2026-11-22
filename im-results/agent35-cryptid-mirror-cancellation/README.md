# Mirror cancellation and the withdrawn #490 blank-root route

> **CRITICAL WITHDRAWAL — 2026-11-22:** The projected CR successor used for the root replay mistranscribes the pinned #85 source branches CR 1,0 / 1,1 / 1,≥2 and the empty-list bump. Therefore the root-chain counts, H-family entry, and 76-step right-insertion target described below are not source-valid. The current append theorem must not be compiled or cited as a proof. See [the CR-branch correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md). The isolated `root_evalStackCfg_DR` definitional equation remains valid.

**Status (22 November 2026):** source-level evaluator algebra restores the connection between the #490 blank start and the no-swap #85 `cfg_DR_n_n` stack trajectory. The projected countdown/reset/H/growth chain has been independently replayed in a V8 persistent-list interpreter using the pinned source branch clauses. This is **not** a Lean proof of the parametric macros or an infinite original-machine execution.

## 1. The two stack swaps cancel

Pinned upstream: Google DeepMind `cryptids` commit [`3647718b5df22e1a61462dec0376bd204526285a`](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a).

In #85's [accelerator module, lines 203–207](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean#L203-L207),
```lean
evalStackCfg .DR_n_n L R = cfg_DR_n_n R L
```
In [`ClosedStackSystem.mirror`, lines 504–518](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/Stack.lean#L504-L518), the mirrored evaluator is
```lean
evalStackCfg m L R := mirrorCfg f (W.evalStackCfg m R L)
```
Composing the definitions gives
```lean
#490.evalStackCfg .DR_n_n L R
  = mirrorCfg f (W.evalStackCfg .DR_n_n R L)
  = mirrorCfg f (cfg_DR_n_n L R)
```
The two argument swaps cancel. The #490 stack lists `L,R` are exactly the arguments to #85's `cfg_DR_n_n L R`; do not swap them again.

The actual #490 [blank-entry theorem, lines 107–115](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean#L107-L115) reaches
```lean
#490.evalStackCfg .DR_n_n [(0,0),(0,0)] [(1,0)]
```
in seven raw TM steps. Its underlying #85 state is therefore exactly
```lean
cfg_DR_n_n [(0,0),(0,0)] [(1,0)]
```
not `cfg_DR_n_n [(1,0)] [(0,0),(0,0)]`.

## 2. First successor from the exact source theorem

Apply #85's `mode_DR_n_n_closed` to `L=[(0,0),(0,0)]`, `R=[(1,0)]`. The branch at [lines 1049–1056](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean#L1049-L1056) is the ordinary (a_1=0,r_1>0) DR branch. It executes four raw steps and returns
```lean
cfg_DR_n_n [(0,0)] [(1,0),(0,0)]
```
The #490 configuration is the mirror of that output. Its projected stack coordinates remain `L=[0], R=[1,0]`. Thus the no-swap projected transition used in `verify_root_corridor_macro.js` is the correct stack transition for the actual #490 root. The current swapped `successor490` in the older `fast_root_stack_sim.js` is wrong.

## 3. Source-transcribed blank-root chain

I independently replayed the projected stack clauses with persistent linked lists, including the token bounce/normalization rules. All target configurations below matched exactly. Raw costs are sums of the pinned `execute n` branches and token-lemma costs; they are still computational/source-transcribed, not kernel checked as one composed theorem.

| Segment | Outer successors | Raw TM steps | Endpoint |
|---|---:|---:|---|
| #490 blank entry | — | 7 | mirror of #85 `cfg_DR_n_n [0,0] [1]` |
| Stack seed → `D_0(540)` | 22,099 | 66,797 | one token event at macro 21,810 |
| First countdown, 180 applications | 133,200 | 399,060 | `D_180(0)` |
| Reset | 1,481 | 2,985 | `D_0(1453)` |
| Second countdown, 484 applications | 946,704 | 2,838,660 | `D_484(1)` |
| c=1 corridor | 9,731 | 31,141 | `H(1939)` |
| 483 H-padding macros | 18,354 | 61,824 | `H(7;Q^966 ++ Hright)` |
| H-base macro | 179 | 591 | first `DR(G,[1] ++ B ++ T)` state |

The root-to-`D_0(540)` prefix is (66,797+7=66,804) raw TM steps. The first and second countdowns were checked for **all** indices used by this trajectory (180 and 484 applications respectively), not only the small (n\le6) regression samples. Each instance matched
[
D_n(c)=CR([0],0^{4n+5}++[c])
\quad\longmapsto\quad
D_{n+1}(c-3)
]
in (8n+24) outer successors and (24n+69) raw steps. The 1,481/2,985 reset also matched.

The first DR/G/B growth seed occurs at outer macro **1,131,748** and costs **3,401,058** raw steps from the stack seed, hence **3,401,065** from blank. The separate tail-parametric insertion candidate
[
S^{76}(DR(G,[1]++B++T))=DR(G,[1]++B++B++T)
]
has 76 outer successors and 254 raw steps in the source-transcribed trace; its opaque-suffix checks show the suffix is not inspected. Repeating it 286 times gives the macro-1,153,484 state with right-stack length 7,330 and raw increment 72,644. The final length is (1+287\cdot12+4+969\cdot4+5=7330).

Definitions:
```text
Q = [12,0,0,0]
G = [0,0,1,0,1,0,0,0,0,1]
B = [16,0,0,0,2,0,0,0,2,0,0,0]
Hright = [2,0,0,0,0]
```

## 4. Candidate invariant correction

The old `fast_root_stack_sim.js` diagnostic (L\in0^*(\epsilon\mid1)), together with its listed mode conditions, is **not** an all-time invariant. In the no-swap root replay, the projected state at macro 1,105,436 is EL with (L) beginning ([0,1,0,\ldots]), hence (L\notin0^*(\epsilon\mid1)). The preceding EL state has right head 1 and a long all-zero (L); the ordinary branches
[
EL(L,[1])\to DL(L,[0])\to EL([0]++\operatorname{bump}(L),[])
]
create the internal 1. This is a concrete failure of the proposed invariant, not a halting event. Any future invariant proof must strengthen the state relation or abandon this predicate.

## 5. Remaining proof obligations

**Exact-source macro preflight status (22 November 2026):** Manual workflow run [44999117485](https://github.com/FlareZ123/bb6/actions/runs/44999117485) successfully built the pinned upstream project and appended the macro, but the first proof attempt failed because `execute 254` was applied while the goal still contained `mirrorCfg f (W.evalStackCfg ...)`; the trace shows `step target` remained under `reflectTape`. The reported `sorryAx` is from that incomplete declaration, not an accepted theorem. Agent 12 updated `RootRightGrowthMacro.append.lean` to rewrite the mirrored evaluator to an explicit `Cfg.headLeft A` tape using the definitional `root_evalStackCfg_DR` equation before `execute 254`. This repair is **not yet compiled**; do not claim the macro has passed Lean or has an accepted axiom profile. Local shell preflight was unavailable in Agent 12's environment, so no second CI run was dispatched. Agent 48's separate run 45000093422 tested the now-withdrawn extra-swap/left-insertion candidate, not this no-swap right-insertion family; its q=5 boundary failure is not evidence against the present candidate. It does reinforce that raw execution proofs must use the correct mirrored configuration and should not be conflated across the two stack orientations.


- Formalize the (D_n) corridor identity for arbitrary (n,c\ge3), including its raw-step count.
- Formalize the 1,481-step reset and the c=1 corridor with exact raw-step accounting.
- Prove the 38-step H-padding, 179-step H-base, and 76-step DR/G/B insertion identities for arbitrary suffixes and their parameter ranges.
- Compose these source theorems through the exact #490 mirrored evaluator and the seven-step blank-entry theorem.
- Audit the transitive axiom profile and ensure no `sorryAx`.

Until those gates pass, the restored root route is a strong computational/source-structural lead, **not** a nonhalting theorem and not a BB(6) solution. Keep it in `im-results/`.


## 2026-11-22 withdrawal of the no-swap macro target

The 76-step right-insertion endpoint in `RootRightGrowthMacro.append.lean`
was derived from Agent 48's projected `NoSwapGrowth.lean`. That projected
function has now been shown to mistranscribe the pinned #85 CR branches
(`1,0`, `1,1`, and `1,≥2`) and the empty-list bump. Therefore the raw
theorem target in the append file is invalid, independently of the earlier
`mirrorCfg/reflectTape` normalization failure. Agent 12's
`root_evalStackCfg_DR` equation remains a correct definitional normal form,
but it does not rescue the invalid endpoint.

**Do not run the current manual workflow for this theorem or cite the 76/254
macro as source-valid.** The old 1,131,748-step root prefix and growth seed
are also withdrawn because the root replay uses the same incorrect CR
transition function. Recompute the root path from the corrected source
clauses before proposing a new raw proof. See
[the critical CR-branch correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md).
