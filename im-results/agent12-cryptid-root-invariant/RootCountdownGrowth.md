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

The finite regression checked six different suffixes: `[]`, `[0]`, `[1]`, `[3,0,0]`, `[7,5,3,1]`, and `[12,0,0,0,12,0,0,0,2]`. All six matched the claimed endpoint, and the 76-step run made zero token-normalizer calls. This is strong computational evidence for a simple symbolic proof: every branch in the 76-step path should depend only on the fixed prefix and leave arbitrary `T` untouched. It is not yet a proof for all finite suffixes.

If the countdown, reset, root-entry path, and arbitrary-suffix insertion are proved against the pinned source, the final identity yields an infinite projected stack orbit from the blank-root seed. The corresponding original-TM nonhalting theorem still requires a kernel-checked lift through the exact #490/#85 source encoding.

## Separate H-phase check

The separate CR H-phase 76-successor insertion also passes the restored source-transcribed regression and makes zero token-normalizer calls. The previous report that it was falsified used the incorrect `b <= 1` DR branch. Its H(7) entry and root reachability are separate obligations; the DR/G/B family above is the current root-connected target.

## Reproducibility and proof obligations

- [`fast_root_stack_sim.js`](./fast_root_stack_sim.js) is the persistent-list root replay.
- [`verify_root_corridor_macro.js`](./verify_root_corridor_macro.js) checks the source branch, 35 countdown samples, the reset, and the two 76-successor macros.
- [`ModeDRBranchAudit.md`](./ModeDRBranchAudit.md) records the pinned-source branch analysis and recovered checkpoints.

The V8 replay and finite suffix tests are computational, not formal. No Lean compilation or transitive axiom audit is claimed. The local shell tool has failed before executing commands; do not replace the required local source preflight with a CI dispatch. Keep all of this in `im-results/` until the exact imported source closure, raw-step correspondence, arbitrary-suffix theorem, and axiom profile have been checked.
