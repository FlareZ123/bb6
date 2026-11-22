# Pinned-source audit: the DR and DL right-head branches are different

> **Mirror correction — 2026-11-22:** The detailed macro-21,810 token event and subsequent `D_n` trace below are for the synthetic #85 trajectory starting at `DR(L=[0,0],R=[1])`; they are not the #490 blank-root path. The #490 wrapper defines `evalStackCfg m L R = mirrorCfg f (W.evalStackCfg m R L)`. Thus its blank-start seed `DR(L=[0,0],R=[1])` corresponds to #85 `DR(L=[1],R=[0,0])`. The correct mirrored #85 simulation has an immediate `tok_CR_1_0_closed` event at macro 0 and does not reach `D_0(540)` at macro 22,099. The old blank-root raw total 66,804 and all claimed root connections through `D_{484}(1)` are withdrawn. The branch-level audit of #85 itself remains useful.

**Status:** source-derived branch correction plus reproducible V8 computation. This is intermediate research, not a Lean theorem or an original-machine nonhalting proof.

## The source split

Pinned upstream: Google DeepMind `cryptids` commit
[`3647718b5df22e1a61462dec0376bd204526285a`](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a).

In `BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`:

- `mode_DL_0_n_closed`, lines 982–1006, splits the right-head first coordinate using `rcases r1 with _ | _ | r5`: 0, 1, and at least 2. Its r1=1 case (lines 994–999) invokes `tok_DR_2_0_closed`.
- `mode_DR_n_n_closed`, lines 1008–1064, instead uses `rcases r1 with _ | r5`: 0 versus positive. The r1=0,a1=0 case (1030–1038) invokes `tok_DR_2_0_closed`; r1=0,a1>0 invokes `tok_CR_1_0_closed`. In the positive branch, a1=0 takes the ordinary four-step DR transition at lines 1049–1056, and a1>0 takes the ordinary three-step CR transition at lines 1057–1064. In particular r1=1 is ordinary, not token-normalized.

The #490 wrapper does change the stack orientation. In the #85 source, `evalStackCfg .DR_n_n L R = cfg_DR_n_n R L` (lines 203–207). `ClosedStackSystem.mirror` defines the transported evaluator as `mirrorCfg f (W.evalStackCfg m R L)` (Stack.lean, lines 504–518). Therefore #490 `DR(L=[0,0],R=[1])` corresponds to #85 `DR(L=[1],R=[0,0])`, not the same ordered pair of stacks.

The actual #490 first successor is the mirror of the #85 `tok_CR_1_0_closed` branch:

| #490 outer successor | State | Evidence |
|---:|---|---|
| 0 | DR([0,0], [1]) | exact 7-raw-step blank entry |
| 1 | CR([1], [0,0,0,1]) | V8 mirror of #85 `DR([1],[0,0])` token closure |

The following table is only the synthetic unmirrored #85 trajectory starting at `DR([0,0],[1])`; it is not the blank-root trace:

The alleged 19-step closure from the root seed is the `mode_DL` r1=1 case misapplied to `mode_DR`.

## Consequence for the proposed 36-step recurrence

The proposed chain from `CR([0,0,1],[c])` reaches `DR([0,0],[1,c+4])` after six outer closures. At that DR state, a1=0 and r1=1, so the pinned source takes the ordinary four-step branch to

`DR([0],[1,0,c+4])`,

not a 19-step token closure to `CR([0,0,1],[c+5])`. Thus the claimed 36-raw-step recurrence and its resulting blank-root nonhalting argument are invalid.

The `b <= 1` edits in the shared simulators transferred the DL r1=1 case into DR. They have been reverted: the DR token branch is now `b === 0` / `b == 0`; the DL r1=1 token branch remains.

## Recovered source-transcribed computations

I reran the persistent-list successor in the available V8 runtime with the source-correct DR split and the independently source-audited token-normalizer corrections. The run reproduces the earlier root checkpoints:

| Macro index | State summary |
|---:|---|
| 24 | DR(L=0001, R=[1,3]) = Corr(3,3) |
| 21,810 | DL(L=0^267 ++ [1], R=[1]), invoking the DR token closure |
| 21,811 | CR(L=0^271 ++ [1], R=[1]) |
| 21,827 | CR(L=0^255 ++ [1], R=[33]) |
| 21,926 | CR(L=0^1561, R=[231]) |
| 22,083 | EL(L=[0], R=[0,546]) |
| 22,099 | D_0(540) |
| 153,843 | D_179(3) |
| 155,299 | D_180(0) |
| 156,780 | D_0(1453) |
| 1,103,484 | D_484(1) |
| 1,113,215 | H(1939) |
| 1,131,748 | first DR/G/B growth seed |
| 1,153,484 | DR(L=G, R=[1] ++ B ++ T), after 286 growth repetitions |

In the synthetic #85 trace, at macro 21,810 the `DL` right-head-1 token closure has input `r3=[]` and `L=0^267 ++ [1]`. The source formula
`closeTokDR(r3,0^n ++ [1]) = CR(L=0^(n+4) ++ [1], R=bump(r3))`
therefore gives `CR(L=0^271 ++ [1],R=[1])` at macro 21,811. This is the exact c=2 corridor token event, not an ordinary DR right-head-1 branch. The token closure costs exactly 1,637 raw steps: the DL branch's `tExecute 4`, 267 `tok_DR_zero` steps at 4 each, one `tok_DR_1_nil_28` at 28, 268 `tok_EL_1` steps at 2 each, and one `tok_EL_exit_zero` at 1. The 21,810 ordinary outer successors before the closure cost 64,565 raw TM steps; the 288 ordinary successors after it cost 595 raw steps to `D_0(540)`. From the synthetic #85 seed, the trace to `D_0(540)` costs 66,797 raw steps; this is not a blank-root total.

Here `D_n(c) = CR(L=[0], R=0^(4n+5) ++ [c])`,
`G=[0,0,1,0,1,0,0,0,0,1]`, and
`B=[16,0,0,0,2,0,0,0,2,0,0,0]`.

The source-transcribed regression now checks:
- 35 instances of `S^(8n+24)(D_n(c)) = D_(n+1)(c-3)` for n=0,…,6 and c in {3,4,5,10,540};
- the 1,481-successor reset `D_180(0) -> D_0(1453)`;
- the c=1 corridor segments `D_484(1) -> F(1939) -> G(1939) -> H(1939)`;
- the 38-successor H-padding macro and 179-successor H-base macro, including opaque suffixes;
- the root-connected H(1939)-to-DR/G/B entry, followed by the 76-successor insertion `S^76(DR(G,[1]++B++T)) = DR(G,[1]++B++B++T)`;
- the separate H-phase CR 76-step insertion, also with zero token-normalizer calls.

## Short root-connected H-family entry

The old 50,000-successor checkpoint is not the first entry into the DR/G/B growth family. The first seed is at macro 1,131,748, reached from D_484(1) in 28,264 outer successors / 93,556 raw TM steps:

| Segment | Outer successors | Raw steps |
|---|---:|---:|
| D_484(1) → F(1939) | 3,897 | 13,641 |
| F(1939) → G(1939) | 5,830 | 17,487 |
| G(1939) → H(1939) | 4 | 13 |
| 483 H-padding macros | 18,354 | 61,824 |
| H-base macro | 179 | 591 |
| **Total** | **28,264** | **93,556** |

For `Q=[12,0,0,0]` and `H(r;R)=CR([0]++(10)^(r+1)++[0,0,1,0,0,0],R)`, the two source-transcribed H-family identities are:

```text
S^38(H(r+4;R)) = H(r;Q++Q++R)                 -- 128 raw steps
S^179(H(7;[a]++T))
  = DR(G,[1]++B++[16,0,0,0]++Q^3++[a]++T), a>=2
                                                   -- 591 raw steps
```

Since 1939=4·484+3, 483 padding macros take H(1939) to H(7;Q^966++[2,0,0,0,0]); the base macro then reaches the first DR/G/B seed with Q^969 in its tail. The 50,000-successor checkpoint at macro 1,153,484 is this first seed followed by 286 repetitions of the 76-step insertion macro. Those repetitions add 21,736 outer successors and 72,644 raw steps.

The countdown raw-cost formula `24n+69` gives 399,060 raw steps for the first 180 countdowns and 2,838,660 for the second 484 countdowns; the reset costs 2,985. These are source-transcribed computations, not yet a quantified Lean proof. The H-phase CR growth loop remains a separate projected identity; the root route here uses H-padding and H-base to reach DR/G/B, not the standalone H-phase CR seed.

The DR/G/B 76-successor macro independently totals **254 raw TM steps**. The count is derived from the actual `execute n` branches in the four source mode lemmas, not transferred from the separate H-phase calculation:

| Source branch | Occurrences | Raw steps each | Subtotal |
|---|---:|---:|---:|
| DR, r1≥1 and a1=0 | 8 | 4 | 32 |
| DR, r1≥1 and a1>0 | 3 | 3 | 9 |
| CR, a1=0 | 13 | 2 | 26 |
| CR, a1=1 and next left value 0 | 8 | 5 | 40 |
| CR, a1=1 and next left value 1 | 2 | 16 | 32 |
| EL, r1>0 | 12 | 1 | 12 |
| DL, r1=0 | 8 | 6 | 48 |
| EL, r1=0 | 16 | 2 | 32 |
| DL, r1≥2 | 4 | 4 | 16 |
| CR, a1=1 and left tail empty | 1 | 6 | 6 |
| DR, left stack empty | 1 | 1 | 1 |
| **Total** | **76** |  | **254** |

The updated `verify_root_corridor_macro.js` computes these costs from the source branch classification and asserts 254 for each tested DR/G/B suffix and for the actual root-reachable state. It also independently checks the H-phase CR macro's raw count (254); equality of the totals is an observed result, not an assumption.

The persistent-list root replay and the finite suffix tests are computational evidence, not an all-time proof. The arbitrary-suffix macro and the long root prefix still need kernel-checked Lean proofs against the pinned source. No Lean compile or axiom audit is claimed. The local shell tool has continued to fail before executing commands, so CI has not been used as a substitute for the required local preflight.

## Next proof target

The useful target is the root-connected countdown/H-family/DR-G-B construction, not the false 19/36-step DR-head-one cycle. Formalize the quantified D_n corridor and reset, the c=1 exit, the H-padding and H-base identities, and the tail-parametric 76-step insertion. Lift the composition through the exact #490/#85 evaluator and prove that the token-normalizer event in the initial root prefix does not halt. Preserve the distinction between source-derived stack dynamics, V8 simulation, and original-TM nonhalting.
