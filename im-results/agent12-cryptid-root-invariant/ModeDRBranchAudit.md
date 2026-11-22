# Pinned-source audit: the DR and DL right-head branches are different

**Status:** source-derived branch correction plus reproducible V8 computation. This is intermediate research, not a Lean theorem or an original-machine nonhalting proof.

## The source split

Pinned upstream: Google DeepMind `cryptids` commit
[`3647718b5df22e1a61462dec0376bd204526285a`](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a).

In `BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`:

- `mode_DL_0_n_closed`, lines 982–1006, splits the right-head first coordinate using `rcases r1 with _ | _ | r5`: 0, 1, and at least 2. Its r1=1 case (lines 994–999) invokes `tok_DR_2_0_closed`.
- `mode_DR_n_n_closed`, lines 1008–1064, instead uses `rcases r1 with _ | r5`: 0 versus positive. The r1=0,a1=0 case (1030–1038) invokes `tok_DR_2_0_closed`; r1=0,a1>0 invokes `tok_CR_1_0_closed`. In the positive branch, a1=0 takes the ordinary four-step DR transition at lines 1049–1056, and a1>0 takes the ordinary three-step CR transition at lines 1057–1064. In particular r1=1 is ordinary, not token-normalized.

The #490 wrapper does not change this conclusion. In the #85 source, `evalStackCfg .DR_n_n L R = cfg_DR_n_n R L` (lines 203–207). `ClosedStackSystem.mirror` defines the transported evaluator as `mirrorCfg f (W.evalStackCfg m R L)` (Stack.lean, lines 504–518), so the two argument swaps cancel. The #490 blank-entry theorem therefore reaches the #85-oriented `DR(L=[0,0], R=[1])` seed after its seven raw steps.

Consequently the exact first outer successors are:

| Outer successor | State | Raw steps in that closure |
|---:|---|---:|
| 0 | DR([0,0], [1]) | seed |
| 1 | DR([0], [1,0]) | 4 |
| 2 | DR([], [1,0,0]) | 4 |
| 3 | EL([0], [1,0,0]) | 1 |

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
| 21,810 | DL(L=0^2671, R=[1]), invoking the DR token closure |
| 21,811 | CR(L=0^2711, R=[1]) |
| 21,827 | CR(L=0^2551, R=[33]) |
| 21,926 | CR(L=0^1561, R=[231]) |
| 22,083 | EL(L=[0], R=[0,546]) |
| 22,099 | D_0(540) |
| 153,843 | D_179(3) |
| 155,299 | D_180(0) |
| 156,780 | D_0(1453) |
| 1,103,484 | D_484(1) |
| 1,153,484 | DR(L=G, R=[1] ++ B ++ T) |

Here `D_n(c) = CR(L=[0], R=0^(4n+5) ++ [c])`,
`G=[0,0,1,0,1,0,0,0,0,1]`, and
`B=[16,0,0,0,2,0,0,0,2,0,0,0]`.

The source-transcribed regression now checks:
- 35 instances of `S^(8n+24)(D_n(c)) = D_(n+1)(c-3)` for n=0,…,6 and c in {3,4,5,10,540};
- the 1,481-successor reset `D_180(0) -> D_0(1453)`;
- the 76-successor insertion `S^76(DR(G,[1]++B++T)) = DR(G,[1]++B++B++T)` for seven numeric suffixes plus an opaque object suffix, with zero token-normalizer calls and explicit suffix-object identity preservation;
- the separate H-phase CR 76-step insertion, also with zero token-normalizer calls.

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

The useful target is again the root-connected countdown/growth construction, not the false 19/36-step DR-head-one cycle. Formalize the exact mode clauses and token closures, then prove the quantified countdown, reset, 50,000-step entry, and tail-parametric 76-step insertion. Preserve the distinction between source-derived stack dynamics, V8 simulation, and original-TM nonhalting.
