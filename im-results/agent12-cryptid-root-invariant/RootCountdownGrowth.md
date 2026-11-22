# Root countdown and growth family — withdrawn candidate

**Critical withdrawal (2026-11-22):** The projected CR transition function used by the old root replay was mistranscribed. Its CR-left-prefix `1,0`, `1,1`, and `1,≥2` branches do not match pinned #85 source `mode_CR_n_n_closed` lines 928–953; its empty-list bump also disagrees with `bumpPairHead`. The 76-step growth macro and all later root checkpoints built from that simulator are withdrawn. See [the correction broadcast](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md).

## Confirmed #490/#85 orientation and initial root steps

The #490 wrapper's two evaluator argument reversals cancel: for every stack mode `m`, `#490.evalStackCfg m L R = mirrorCfg f (#85.cfg_m L R)`. The state map is `f = ![5,4,2,0,1,3]`. This source-level orientation result remains valid.

The #490 blank-entry theorem gives the seven-raw-step entry to the mirror of #85 `DR(L=[0,0],R=[1])`. The first two #85 DR successors are also source-checked ordinary branches:
- at raw time 7: `DR(L=[0,0],R=[1])`;
- right head 1 / left head 0 uses `execute 4`, reaching `DR(L=[0],R=[1,0])` at raw time 11;
- the next right-head-1 / left-head-0 branch uses `execute 4`, reaching `DR(L=[],R=[1,0,0])` at raw time 15.

No later projected root checkpoint in the old simulator is currently trusted. The corrected #490/D0 raw-time-36 alignment recorded in `DeepMindStackReduction.md` is an independent checkpoint; the full continuation from raw time 15 must be recomputed with source-accurate branches.

## Withdrawn projected root prefix

The old `fast_root_stack_sim.js` and `verify_root_corridor_macro.js` use the incorrect CR branches. Consequently, their macro indices, token-event location, 1,131,748-step prefix, 1,153,484 growth seed, and all derived reset/corridor/H/growth counts are untrusted. In particular, the old claim of a root-connected 76-step right-insertion macro is false as a source-projection claim. The current `RootRightGrowthMacro.append.lean` and its config-normalization patch target that invalid endpoint; do not compile or cite them as a proof.

## Surviving D-countdown recurrence

The independent direct (D_n(c)) factorization uses only CR-left-zero and CR-empty, plus ordinary EL/DL/DR branches; it does not use any of the mistranscribed CR-left-one branches. It survives the specific CR correction and is preserved in [RootCountdownSweep.md](./RootCountdownSweep.md). Its quantified Lean proof and #490 mirror lift remain outstanding. The earlier shared-corridor derivation and its 180/484 regression counts were produced by the incorrect simulator and are not evidence for the recurrence.

## Withdrawn reset/corridor/H/growth archive

The following sections are retained as historical experimental material only. Their root connectivity and macro counts were computed with the incorrect CR projection and must not be used. Recompute them from the pinned source after correcting every projected branch.

## WITHDRAWN reset and second-countdown candidate

The reset follows from the c=0 corridor macro. Since `D_180(0)=S^724(Corr(723,0))`, and `Corr(723,0)` reaches `Corr(3,1453)` in `3·723+32=2201` successors, followed by the 4-successor shared corridor to `D_0(1453)`, the remaining path from `D_180(0)` is

```text
2201 - 724 + 4 = 1481 outer successors.
```

The source-transcribed reset is

```text
D_180(0) --1481 outer successors / 2985 raw steps--> D_0(1453).
```

The second countdown applies the same candidate family 484 times:

```text
D_0(1453) --946704 outer successors--> D_484(1).
```

Its raw-step total from the sampled formula is 2,838,660. Thus the D_0(540)-to-D_484(1) segment has 1,081,385 outer successors and 3,240,705 raw steps. The persistent-list root replay places `D_484(1)` at macro 1,103,484.

The raw formula `24n+69` and its countdown aggregates remain computational/source-transcribed until the quantified corridor lemma is kernel-checked. From the stack seed, the projected costs are 3,307,502 to `D_484(1)`, 3,401,058 to the first DR/G/B seed, and 3,473,702 to the macro-1,153,484 checkpoint. Add seven raw steps for the blank-entry theorem: the corresponding blank-root totals are 3,307,509; 3,401,065; and 3,473,709.

## WITHDRAWN c=1 corridor candidate

Write

```text
Corr(r,c) = DR(L=0^r ++ [1], R=[1,c]).
F(r) = EL(L=0^4, R=[1,0,0,0] ++ (10)^(r+2) ++ [3]).
G(r) = DR(L=[0,0] ++ (10)^(r+2) ++ [0,0,1,0,0,0], R=[1,0]).
H(r) = CR(L=[0] ++ (10)^(r+1) ++ [0,0,1,0,0,0], R=[2,0,0,0,0]).
```

Here `(10)^j` means j repetitions of the pair `[1,0]`. Since `D_484(1)` is the shared-corridor output from `Corr(1939,1)`, the source-transcribed c=1 path is:

| Segment | Outer successors | Raw TM steps |
|---|---:|---:|
| D_484(1) → F(1939) | 3,897 | 13,641 |
| F(1939) → G(1939) | 5,830 | 17,487 |
| G(1939) → H(1939) | 4 | 13 |
| **Total** | **9,731** | **31,141** |

No token-normalizer call occurs in these three segments. The finite corridor regression checks r=1,…,8; the r=1939 instance is separately replayed.

## WITHDRAWN H-family entry candidate

Let

```text
Q = [12,0,0,0]
H(r;R) = CR(L=[0] ++ (10)^(r+1) ++ [0,0,1,0,0,0], R).
```

Two short parametric macros replace the earlier 50,000-successor finite entry.

### Padding macro

```text
S^38(H(r+4;R)) = H(r; Q ++ Q ++ R)
```

for r≥0 and arbitrary finite right suffix R. This macro costs **128 raw TM steps**, makes no token-normalizer call, and removes four `[1,0]` pairs from the left stack while prepending two Q blocks to the right. The checked-in regression tests r=0,…,7,11,1935 with several distinct suffixes, including an opaque object suffix. The #85 closed-stack encoding has all eight hparams equal to 1, so the second coordinate of every StackTuple(2) pair is ignored by the tape encoding; the first-coordinate V8 simulator therefore covers arbitrary pair-list suffixes. The branch histogram is constant across the tested r and R values:

| Source branch | Count | Cost | Subtotal |
|---|---:|---:|---:|
| CR, left head 0 | 14 | 2 | 28 |
| CR, left head 1 / next-left 0 | 2 | 5 | 10 |
| CR, left head 1 / next-left 1 | 2 | 16 | 32 |
| EL, right head 0 | 6 | 2 | 12 |
| EL, right head positive | 4 | 1 | 4 |
| DL, right head 0 | 2 | 6 | 12 |
| DL, right head ≥2 | 2 | 4 | 8 |
| DR, left head 0 / right head positive | 4 | 4 | 16 |
| DR, left head positive / right head positive | 2 | 3 | 6 |
| **Total** | **38** | | **128** |

### Base macro

The base transformation is stronger than a fixed `Q^m` prefix. For every a≥2 and arbitrary finite pair-list suffix T:

```text
S^179(H(7; [a] ++ T))
  = DR(L=G, R=[1] ++ B ++ [16,0,0,0] ++ Q^3 ++ [a] ++ T).
```

Here `[a]` denotes the pair-stack head `[(a,0)]`. The Lean target takes T as an arbitrary finite pair-list suffix. Since the #85 closed-stack encoding has all eight hparams equal to 1, the second coordinate of each StackTuple(2) pair is ignored; the first-coordinate V8 tests therefore cover the full pair-list encoding. The root application has `[a]=[(12,0)]` because its right stack begins with Q.

with

```text
G = [0,0,1,0,1,0,0,0,0,1]
B = [16,0,0,0,2,0,0,0,2,0,0,0].
```

It costs **591 raw TM steps**, with no token-normalizer calls. The regression tests a in {2,3,4,5,12,100,100000} with empty, numeric, and opaque suffixes; the opaque suffix is preserved by identity. The 179-step branch histogram is constant across these tested heads and suffixes:

| Source branch | Count | Cost | Subtotal |
|---|---:|---:|---:|
| CR, left head 0 | 44 | 2 | 88 |
| CR, left head 1 / next-left 0 | 15 | 5 | 75 |
| CR, left head 1 / next-left 1 | 6 | 16 | 96 |
| CR, left head 1 / left tail nil | 2 | 6 | 12 |
| EL, right head 0 | 35 | 2 | 70 |
| EL, right head positive | 25 | 1 | 25 |
| DL, right head 0 | 15 | 6 | 90 |
| DL, right head ≥2 | 10 | 4 | 40 |
| DR, left head 0 / right head positive | 18 | 4 | 72 |
| DR, left head positive / right head positive | 7 | 3 | 21 |
| DR, left tail nil | 2 | 1 | 2 |
| **Total** | **179** | | **591** |

### WITHDRAWN application to the root

Since `1939 = 4·484 + 3`, apply the padding macro 483 times:

```text
H(1939;Hright)
  --18,354 outer / 61,824 raw-->
H(7;Q^966 ++ Hright).
```

The base macro sees the first pair `(12,0)` and preserves the rest of the right stack:

```text
H(7;Q^966 ++ Hright)
  --179 outer / 591 raw-->
DR(L=G, R=[1] ++ B ++ [16,0,0,0] ++ Q^3 ++ Q^966 ++ Hright)
= DR(L=G, R=[1] ++ B ++ [16,0,0,0] ++ Q^969 ++ Hright).
```

Thus the first root-connected DR/G/B seed is reached from `D_484(1)` after **28,264 outer successors and 93,556 raw TM steps**, at macro **1,131,748**. Its right-list length is 3,898.

The earlier 50,000-successor checkpoint is later than this first entry: it is the first seed followed by 286 repetitions of the 76-successor insertion macro. Those repetitions add 21,736 outer successors and 72,644 raw steps, giving the previously recorded macro 1,153,484 state with right-list length 7,330. The full D_484(1)-to-checkpoint segment costs 166,200 raw steps.

## WITHDRAWN projected #85 tail-parametric growth

The candidate insertion identity is

```text
S^76(DR(L=G, R=[1] ++ B ++ T))
  = DR(L=G, R=[1] ++ B ++ B ++ T)
```

for every finite suffix T. The 76 outer successors independently total **254 raw TM steps**, derived from the pinned `execute n` branches rather than borrowed from the separate H-phase macro.

The checked-in regression tests seven numeric suffixes plus an opaque object suffix, verifies object identity preservation, and checks the actual root-reachable seed. No token-normalizer call occurs. The separate H-phase CR 76-step identity also has a separately checked 254-step cost, but it is not the root-connected route used here.

If the countdown, reset, c=1 corridor, H-padding, H-base, and DR/G/B insertion identities are proved against the pinned source, their composition yields an infinite projected stack orbit from the blank-root seed. The source-transcribed computations are not yet kernel-checked Lean proofs or an original-TM nonhalting theorem.

## Source target and encoding facts (macro theorem withdrawn)

The intended original-source proof target is the real #490 wrapper module at upstream `google-deepmind/cryptids` commit `3647718b5df22e1a61462dec0376bd204526285a`:

```text
BusyBeaver/BB6/Accelerations/
  M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean
```

This file imports the #85 module

```text
BusyBeaver/BB6/Accelerations/
  M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean
```

and explicitly defines the state relabelling `f = ![5,4,2,0,1,3]`, transition isomorphism `hM`, and

```lean
def closedStackSystem : ClosedStackSystem target :=
  M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.mirror f
    M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.encLeft_eq_encRight hM
```

The #85 stack type is `StackTuple 2 = ℕ × ℕ`. Its `closedStackSystem` sets `dSym=1`, `sSym=0`, and all eight parameters `strideL,offsetL,sepL,maxSepL,strideR,offsetR,sepR,maxSepR` to 1. Hence each pair `(a,b)` encodes `1^(a+1)0^1`, because `stackSepLen 1 1 b = 1` independently of b. The second coordinate is semantically ignored by the tape encoding. However, the checked-in JS transition function is not source-exact: its CR branches and empty-list bump were mistranscribed. Do not infer correctness of a simulator merely from the encoding projection.

The same #490 file contains `init_reaches_nontrivial`, the exact 7-raw-step blank-start entry to `closedStackSystem.evalStackCfg .DR_n_n [(0,0),(0,0)] [(1,0)]`. Thus the initial mirrored stack state is an actual upstream source theorem. This does not validate any later projected root replay.

In this #490 module, `execute n` is a local tactic macro that iterates n raw `ReachesPlus.head` steps and discharges each with the original `Tape.move`/`Tape.write` semantics. Therefore `execute 128`, `execute 591`, and `execute 254` mean exactly 128, 591, and 254 primitive TM transitions, respectively—not outer stack successors. The outer counts 38, 179, and 76 are projected-stack successors; their raw counts are proved separately.

The `root_evalStackCfg_DR` definitional normal-form equation remains correct, but the current `RootRightGrowthMacro.append.lean` theorem target is invalid because its projected endpoint was derived from the mistranscribed CR function. Do not dispatch the associated workflow for that theorem. The #85-side `reachesPlus_mirrorCfg` transport remains available for any future source-accurate path.

## Reproducibility status after CR correction

- [`fast_root_stack_sim.js`](./fast_root_stack_sim.js) is the historical persistent-list replay; it uses the incorrect CR projection and is withdrawn.
- [`verify_root_corridor_macro.js`](./verify_root_corridor_macro.js) checks the same incorrect projected transition function; its macro and root-path assertions are withdrawn.
- [`ModeDRBranchAudit.md`](./ModeDRBranchAudit.md) records the pinned-source DR branch distinction and the corrected initial DR steps only; it does not validate the withdrawn full root path.
- [`RootCorridorMacro.md`](./RootCorridorMacro.md) contains historical shared-corridor and c=1 identities from the withdrawn projected model; do not rely on them.

No Lean compile or transitive axiom audit is claimed. The local shell tool has failed before executing commands. The next valid proof target is the source-accurate D_n recurrence in RootCountdownSweep.md; independently correct and audit the full projected transition function before attempting any root continuation. The previous 76-step macro theorem target is invalid even though the isolated `root_evalStackCfg_DR` definitional equation remains correct.


### 2026-11-22 correction history and CR-branch withdrawal

The earlier 260-step left-insertion seed, its 29-step token closure, and
750,000 / 1,153,484 iterates belong to Agent 48's extra-swap abstract system
and are not the #490 blank-root orbit.

A later no-swap candidate was then proposed after the evaluator double-swap
cancellation was established. That candidate is also withdrawn: its projected
CR 1,0 / 1,1 / 1,≥2 updates do not match the pinned #85 source, and its empty
`bumpPairHead` case was wrong. Thus the old 22,099-step root prefix, 1,131,748
growth seed, 76-successor insertion, and associated raw totals are not valid
evidence.

The only surviving results in this dossier are the evaluator orientation
identity, the exact seven-step blank entry, the two ordinary DR successors
through raw time 15, and the direct D-countdown sweep derivation in
[`RootCountdownSweep.md`](./RootCountdownSweep.md). The corrected #490/D0
raw-time-36 checkpoint is documented separately in
[`DeepMindStackReduction.md`](../agent32-cryptid-padding/DeepMindStackReduction.md).
No complete root-to-cylinder path, infinite orbit, halting proof, nonhalting
proof, or BB(6) value is established.
