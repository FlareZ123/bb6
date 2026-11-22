# Root countdown and growth family

**Status: source-transcribed candidate, not a formal nonhalting proof.** The previous blanket withdrawal of this construction was based on a misreading of `mode_DR_n_n_closed`. In the pinned #85 source, `mode_DR` tokenizes only right-head 0; positive right heads, including 1, take the ordinary branch. The separate `mode_DL` rule is the one that splits right-head 0, 1, and ≥2. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md).

All macro indices below count **outer stack successors**. Raw TM-step costs are stated separately and derived from the source `execute n` branches. The initial #490 blank-root prefix reaches the #85-oriented seed `DR(L=[0,0],R=[1])` after 7 raw TM steps.

## #490 mirror cancellation and projected root checkpoints

The #490 wrapper's evaluator is `mirrorCfg f (W.evalStackCfg m R L)`, while #85's evaluator is `cfg_DR_n_n R L`. Therefore the two stack-argument reversals cancel:
`#490.evalStackCfg .DR_n_n L R = mirrorCfg f (cfg_DR_n_n L R)`.
The seven-step blank-entry theorem reaches the mirror of #85 `cfg_DR_n_n [0,0] [1]`; the projected lists are not swapped before applying the #85 `cfg_DR_n_n` transition clauses.

The first source successor is the ordinary DR branch (a_1=0,r_1=1>0), costing four raw steps and taking `DR([0,0],[1])` to `DR([0],[1,0])`. The first token event is the DL right-head-1 closure at macro 21,810. The no-swap projected replay then reaches:
- macro 22,099: `D_0(540)`;
- macro 155,299: `D_180(0)`;
- macro 156,780: `D_0(1453)`;
- macro 1,103,484: `D_484(1)`;
- macro 1,113,215: `H(1939)`;
- macro 1,131,748: first `DR/G/B` right-insertion seed.

## Blank-root-connected projected prefix

At macro 21,810 the state is `DL(L=0^267 ++ [1], R=[1])`. The DL right-head-1 branch invokes the DR token closure with `r3=[]`.
The source-exact token identity `closeTokDR(r3,0^n ++ [1]) = CR(L=0^(n+4) ++ [1],R=bump(r3))` gives `CR(L=0^271 ++ [1],R=[1])` at macro 21,811. This is the c=2 corridor from `Corr(263,2)` at macro 21,271. Its 556-successor identity reaches `CR(L=0^255 ++ [1],R=[33])` at macro 21,827. A further 256 outer successors reach `EL(L=[0],R=[0,546])` at macro 22,083; 16 more reach `D_0(540)` at macro 22,099.

The token closure has an exact source-step count. The DL right-head-1 branch first executes 4 raw steps to enter `tok_DR`; the closure then uses 267 `tok_DR_zero` applications (4 each), one `tok_DR_1_nil_28` (28), 268 `tok_EL_1` applications (2 each), and one `tok_EL_exit_zero` (1):

```text
4 + 267·4 + 28 + 268·2 + 1 = 1,637 raw TM steps.
```

The 21,810 ordinary successors before the token closure cost 64,565 raw TM steps. The 288 ordinary successors after the closure cost 595 raw steps to `D_0(540)`. Thus the stack seed to `D_0(540)` costs 66,797 raw steps; adding the seven-step blank-entry theorem gives **66,804 raw TM steps from blank**. This is a DL right-head-1 closure; it does not contradict the separate rule that DR right-head 1 is ordinary.

## Projected #85 countdown

Define

```text
D_n(c) = CR(L=[0], R=0^(4n+5) ++ [c]).
```

The candidate countdown identity is

```text
S^(8n+24)(D_n(c)) = D_(n+1)(c-3),   c >= 3.
```

This identity follows algebraically from the shared-corridor family. Set `r=4n+3`. Then `D_n(c)` is the shared-corridor output `S^(r+1)(Corr(r,c))). The c≥3 corridor macro takes `Corr(r,c)` to `Corr(r+4,c-3)` in `2r+14` successors; the latter reaches `D_(n+1)(c-3)` in `r+5` more successors. Removing the initial `r+1` shared-corridor segment leaves

```text
(2r+14) - (r+1) + (r+5) = 2r+18 = 8n+24.
```

The source-transcribed regression checks n=0,…,6 and c in {3,4,5,10,540}. Its raw cost on these paths is

```text
24n + 69 raw TM steps.
```

The raw-cost formula is still an observed/source-counted formula, not a quantified Lean theorem.

The root replay gives:

| Macro index | State |
|---:|---|
| 22,099 | D_0(540) |
| 153,843 | D_179(3) |
| 155,299 | D_180(0) |

The first countdown has 180 applications, 133,200 outer successors, and 399,060 raw steps.

## Projected #85 reset and second countdown

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

The raw formula `24n+69` and its countdown aggregates remain computational/source-transcribed until the quantified corridor lemma is kernel-checked. From the synthetic #85 seed (not from the blank tape), the projected costs are 3,307,502 to `D_484(1)`, 3,401,058 to the first DR/G/B seed, and 3,473,702 to the 50,000-successor projected checkpoint. All earlier blank-to-these-state totals are withdrawn.

## Projected #85 c=1 corridor to H(1939)

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

## Projected #85 H-family entry into the DR/G/B growth family

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

### Applying the family to the root

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

## Projected #85 tail-parametric growth

The candidate insertion identity is

```text
S^76(DR(L=G, R=[1] ++ B ++ T))
  = DR(L=G, R=[1] ++ B ++ B ++ T)
```

for every finite suffix T. The 76 outer successors independently total **254 raw TM steps**, derived from the pinned `execute n` branches rather than borrowed from the separate H-phase macro.

The checked-in regression tests seven numeric suffixes plus an opaque object suffix, verifies object identity preservation, and checks the actual root-reachable seed. No token-normalizer call occurs. The separate H-phase CR 76-step identity also has a separately checked 254-step cost, but it is not the root-connected route used here.

If the countdown, reset, c=1 corridor, H-padding, H-base, and DR/G/B insertion identities are proved against the pinned source, their composition yields an infinite projected stack orbit from the blank-root seed. The source-transcribed computations are not yet kernel-checked Lean proofs or an original-TM nonhalting theorem.

## Exact Lean source target and raw-step semantics

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

The #85 stack type is `StackTuple 2 = ℕ × ℕ`. Its `closedStackSystem` sets `dSym=1`, `sSym=0`, and all eight parameters `strideL,offsetL,sepL,maxSepL,strideR,offsetR,sepR,maxSepR` to 1. Hence each pair `(a,b)` encodes `1^(a+1)0^1`, because `stackSepLen 1 1 b = 1` independently of b. The second coordinate is semantically ignored by the tape encoding; the JS first-coordinate stack simulator is therefore exact for arbitrary pair-list suffixes, not merely suffixes with second coordinate zero.

The same #490 file contains `init_reaches_nontrivial`, the exact 7-raw-step blank-start entry to `closedStackSystem.evalStackCfg .DR_n_n [(0,0),(0,0)] [(1,0)]`. Thus the mirrored #490 target is not an assumed path: it is an actual upstream source module with an explicit transition-table and stack-system mirror from #85.

In this #490 module, `execute n` is a local tactic macro that iterates n raw `ReachesPlus.head` steps and discharges each with the original `Tape.move`/`Tape.write` semantics. Therefore `execute 128`, `execute 591`, and `execute 254` mean exactly 128, 591, and 254 primitive TM transitions, respectively—not outer stack successors. The outer counts 38, 179, and 76 are projected-stack successors; their raw counts are proved separately.

The natural append target for proving the *mirrored* H-padding, H-base, and DR/G/B raw lemmas is this #490 wrapper, reusing its actual `closedStackSystem`, `target`, and `execute` definitions. The #85-side formulas tested in this file have not yet been lifted to that mirror; no root connection follows until that lift and the corrected root replay are established. The existing manual workflow `.github/workflows/agent32-hphase-growth-macro.yml` checks out the same upstream commit and builds this exact module. Its current Lean pin is v4.35.0-rc4; the uploaded local Lean 4.36.0-rc2 preflight has not succeeded in this runtime, so no CI dispatch is claimed.

## Reproducibility and proof obligations

- [`fast_root_stack_sim.js`](./fast_root_stack_sim.js) is the persistent-list root replay.
- [`verify_root_corridor_macro.js`](./verify_root_corridor_macro.js) checks the source branch, corridor samples, token closures, countdown samples and costs, reset, c=1 corridor, H-padding and H-base macros, root entry, 76-step insertion, and raw-step totals.
- [`ModeDRBranchAudit.md`](./ModeDRBranchAudit.md) records the pinned-source branch distinction and the recovered root path.
- [`RootCorridorMacro.md`](./RootCorridorMacro.md) contains the shared-corridor and c=1 family identities underlying the entry.

No Lean compile or transitive axiom audit is claimed. The local shell tool has failed before executing commands; CI has not been used as a substitute for the required local preflight. The next proof target is to formalize the quantified D_n corridor, reset, c=1 exit, H-padding, H-base, and 76-step DR/G/B insertion, then compose them through the exact #490/#85 encoding.


### 2026-11-22 corrected mirrored-root nonhalting route

The root replay's pumping state is already reached at outer successor 260.
At that point the state is DR with left length 31 and right length 14:

    B  = [0,2,0,0,0,2,0,0,0,16,0,0]
    R0 = [0,1,0,0,0,0,0,0,0,0,1,0,0,0]
    T0 = [0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0]

    DR([1] ++ B ++ T0, R0).

The 750,000 and 1,153,484 checkpoints are later macro iterates:
750000-260 = 9865*76 and 1153484-260 = 15174*76. The root-entry task is
therefore only 260 outer successors.

The blank-root prefix has an independently audited raw-step split:
7 steps to DR([0,0],[1]), 29 steps for the initial token closure to the
post-token CR state, and 848 steps for the next 259 ordinary successors.
Total: 884 raw TM steps. The 29-step token path is 3 + 2 + 21 + 2 + 1;
the 848-step ordinary path has branch counts recorded in
[Agent 48's mirrored-root dossier](../agent48-mirrored-root-growth/README.md).

The 76-successor macro is
DR([1] ++ B ++ T,R0) -> DR([1] ++ B ++ B ++ T,R0) for arbitrary suffix T,
at cost 254 raw TM steps. The new source append attempts to prove the token
closure, ordinary prefix, blank-root reachability, macro, and then
IsNotHalt.of_reachesPlus_invariant. If all exact-source theorems compile
with clean axiom profiles, this proves #490 nonhalting from blank start.
Until CI succeeds, keep this as a proof attempt, not an established
nonhalting result. It does not determine BB(6).
