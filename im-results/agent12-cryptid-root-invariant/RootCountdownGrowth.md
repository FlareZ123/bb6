# Root countdown and growth family

**Status: source-transcribed candidate, not a formal nonhalting proof.** The previous blanket withdrawal of this construction was based on a misreading of `mode_DR_n_n_closed`. In the pinned #85 source, `mode_DR` tokenizes only right-head 0; positive right heads, including 1, take the ordinary branch. The separate `mode_DL` rule is the one that splits right-head 0, 1, and ≥2. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md).

All macro indices below count **outer stack successors**. Raw TM-step costs are stated separately and derived from the source `execute n` branches. The initial #490 blank-root prefix reaches the #85-oriented seed `DR(L=[0,0],R=[1])` after 7 raw TM steps.

## Root-connected countdown

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

## Reset and second countdown

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

The raw formula `24n+69` and its aggregates remain computational/source-transcribed until the quantified corridor lemma is kernel-checked.

## The root's c=1 corridor to H(1939)

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

## Parametric H-family entry into the DR/G/B growth family

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

for r≥0 and arbitrary finite right suffix R. This macro costs **128 raw TM steps**, makes no token-normalizer call, and removes four `[1,0]` pairs from the left stack while prepending two Q blocks to the right. The checked-in regression tests r=0,…,7,11,1935 with several distinct suffixes, including an opaque object suffix. The branch histogram is constant across the tested r and R values:

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

Here `[a]` denotes the pair-stack head `[(a,0)]`. The Lean target takes T as a finite pair-list suffix; the current V8 tests cover numeric first-coordinate tails (second coordinate zero) and an opaque sentinel, while arbitrary nonzero second coordinates remain to be discharged by the source proof. The root application has `[a]=[(12,0)]` because its right stack begins with Q.

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

## Tail-parametric growth

The candidate insertion identity is

```text
S^76(DR(L=G, R=[1] ++ B ++ T))
  = DR(L=G, R=[1] ++ B ++ B ++ T)
```

for every finite suffix T. The 76 outer successors independently total **254 raw TM steps**, derived from the pinned `execute n` branches rather than borrowed from the separate H-phase macro.

The checked-in regression tests seven numeric suffixes plus an opaque object suffix, verifies object identity preservation, and checks the actual root-reachable seed. No token-normalizer call occurs. The separate H-phase CR 76-step identity also has a separately checked 254-step cost, but it is not the root-connected route used here.

If the countdown, reset, c=1 corridor, H-padding, H-base, and DR/G/B insertion identities are proved against the pinned source, their composition yields an infinite projected stack orbit from the blank-root seed. The source-transcribed computations are not yet kernel-checked Lean proofs or an original-TM nonhalting theorem.

## Reproducibility and proof obligations

- [`fast_root_stack_sim.js`](./fast_root_stack_sim.js) is the persistent-list root replay.
- [`verify_root_corridor_macro.js`](./verify_root_corridor_macro.js) checks the source branch, corridor samples, token closures, countdown samples and costs, reset, c=1 corridor, H-padding and H-base macros, root entry, 76-step insertion, and raw-step totals.
- [`ModeDRBranchAudit.md`](./ModeDRBranchAudit.md) records the pinned-source branch distinction and the recovered root path.
- [`RootCorridorMacro.md`](./RootCorridorMacro.md) contains the shared-corridor and c=1 family identities underlying the entry.

No Lean compile or transitive axiom audit is claimed. The local shell tool has failed before executing commands; CI has not been used as a substitute for the required local preflight. The next proof target is to formalize the quantified D_n corridor, reset, c=1 exit, H-padding, H-base, and 76-step DR/G/B insertion, then compose them through the exact #490/#85 encoding.
