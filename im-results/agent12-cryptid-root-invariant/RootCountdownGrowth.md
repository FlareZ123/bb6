# Root countdown and growth family

**Status: source-transcribed candidate, not a formal nonhalting proof.** The previous withdrawal of this construction was based on a misreading of `mode_DR_n_n_closed`. In the pinned #85 source, `mode_DR` tokenizes only right-head 0; positive right heads, including 1, take the ordinary branch. The separate `mode_DL` rule is the one that splits right-head 0, 1, and ≥2. The restored simulators now follow that distinction. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md).

All macro indices below count **outer stack successors**, not raw Turing-machine steps. The initial #490 blank-root prefix reaches the #85-oriented seed `DR(L=[0,0],R=[1])` after 7 raw TM steps.

## Root-connected countdown

Define

```text
D_n(c) = CR(L=[0], R=0^(4n+5) ++ [c]).
```

The candidate countdown identity is

```text
S^(8n+24)(D_n(c)) = D_(n+1)(c-3),   c >= 3.
```

A source-transcribed array regression checked 35 parameter pairs: n=0,…,6 and c in {3,4,5,10,540}. The persistent-list root replay gives the following checkpoints:

| Macro index | State |
|---:|---|
| 22,099 | D_0(540) |
| 153,843 | D_179(3) |
| 155,299 | D_180(0) |

The first countdown comprises 180 applications, with total length

`sum_(n=0)^179 (8n+24) = 133,200` outer successors.

## Reset and second countdown

The source-transcribed successor has the finite reset

```text
D_180(0) --1481 successors--> D_0(1453).
```

The second countdown applies the same sampled family 484 times:

```text
D_0(1453) --946704 successors--> D_484(1).
```

The arithmetic is `1453 - 3*484 = 1` and

`sum_(n=0)^483 (8n+24) = 946,704`.

The persistent-list root replay places `D_0(1453)` at macro 156,780 and `D_484(1)` at macro 1,103,484. These long segments have computational support from the source-transcribed interpreter; they are not yet Lean theorems.

## Root-reachable DR/G/B growth family

A further 50,000 outer successors from `D_484(1)` reach macro 1,153,484 in

```text
DR(L=G, R=[1] ++ B ++ T)
G = [0,0,1,0,1,0,0,0,0,1]
B = [16,0,0,0,2,0,0,0,2,0,0,0]
```

where `T` is the remaining finite right-list suffix. The replayed root state has right-list length 7,330 and begins with `[1] ++ B`.

The candidate tail-parametric insertion identity is

```text
S^76(DR(L=G, R=[1] ++ B ++ T))
  = DR(L=G, R=[1] ++ B ++ B ++ T).
```

The checked-in regression now tests seven numeric suffixes plus an opaque object suffix; all matched the claimed endpoint, and the 76-step run made zero token-normalizer calls. A separate V8 test used an opaque linked-list sentinel and confirmed that the identical sentinel survives untouched. These are strong computational indications that every branch depends only on the fixed prefix, but they are not a proof for all finite suffixes.

### Raw TM-step count, derived from the actual source branches

The 76 outer successors independently total **254 raw TM steps**. This is not transferred from the separate H-phase macro: each branch of the DR/G/B path was classified against the pinned `execute n` calls in `mode_CR_n_n_closed`, `mode_EL_n_n_closed`, `mode_DL_0_n_closed`, and `mode_DR_n_n_closed`.

| Source branch on this path | Occurrences | Raw steps each | Subtotal |
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

No DR r1=0 token branch or DL r1=1 token branch occurs in this macro. The checked-in `sourceClosureCost` regression computes the sum from the source branch classification and asserts 254 for each tested suffix, including the actual root-reachable state. The raw-step count is therefore independently derived for this DR/G/B macro, not assumed from H-phase.

If the countdown, reset, root-entry path, and arbitrary-suffix insertion are proved against the pinned source, the final identity yields an infinite projected stack orbit from the blank-root seed. The corresponding original-TM nonhalting theorem still requires a kernel-checked lift through the exact #490/#85 source encoding.

## Separate H-phase check

The separate CR H-phase 76-successor insertion also passes the restored source-transcribed regression and makes zero token-normalizer calls. The previous report that it was falsified used the incorrect `b <= 1` DR branch. Its H(7) entry and root reachability are separate obligations; the DR/G/B family above is the current root-connected target.

## Reproducibility and proof obligations

- [`fast_root_stack_sim.js`](./fast_root_stack_sim.js) is the persistent-list root replay.
- [`verify_root_corridor_macro.js`](./verify_root_corridor_macro.js) checks the source branch, 35 countdown samples, the reset, the root-connected 76-successor macro, its 254-raw-step count, and opaque-suffix preservation.
- [`ModeDRBranchAudit.md`](./ModeDRBranchAudit.md) records the pinned-source branch analysis and recovered checkpoints.

The V8 replay and finite suffix tests are computational, not formal. No Lean compilation or transitive axiom audit is claimed. The local shell tool has failed before executing commands; do not replace the required local source preflight with a CI dispatch. Keep all of this in `im-results/` until the exact imported source closure, raw-step correspondence, arbitrary-suffix theorem, and axiom profile have been checked.


## Raw TM cost of the root-reachable 76-step macro

The DR/G/B insertion macro is also exactly **254 raw TM steps**, not merely 76 outer stack successors. I classified each of its 76 states under the pinned #85 source mode closures and summed the exact execute lengths:

| Source branch | Occurrences | Raw steps each | Subtotal |
|---|---:|---:|---:|
| DR, left head 0 and right head positive | 8 | 4 | 32 |
| DR, left head positive and right head positive | 3 | 3 | 9 |
| CR, left head 0 | 13 | 2 | 26 |
| CR, left head 1, second head 0 | 8 | 5 | 40 |
| CR, left head 1, second head 1 | 2 | 16 | 32 |
| EL, right head positive | 12 | 1 | 12 |
| DL, right head 0 | 8 | 6 | 48 |
| EL, right head 0 | 16 | 2 | 32 |
| DL, right head greater than 1 | 4 | 4 | 16 |
| CR, left head 1 with empty tail | 1 | 6 | 6 |
| DR, empty left list | 1 | 1 | 1 |
| **Total** | **76** |  | **254** |

No branch in this path invokes a token normalizer. The branch-count multiset is the same as the separate H-phase 76-step macro's 254-step certificate, although the state sequence and starting family differ.

This gives a direct Lean target in the #490 wrapper module, with arbitrary finite suffix T:

- start: closedStackSystem.evalStackCfg .DR_n_n G ([1] ++ B ++ T)
- end: closedStackSystem.evalStackCfg .DR_n_n G ([1] ++ B ++ B ++ T)
- raw reachability: execute 254

Use the public ClosedStackSystem.evalStackCfg field, not the private evalStackCfg definition from the #85 module. A previous CI attempt failed solely because the patch named the private definition; the patch script has been updated to use the public field, but has not yet passed local Lean preflight or CI. This is a branch-counted proof target, not a compiled theorem.
