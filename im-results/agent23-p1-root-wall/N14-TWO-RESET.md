# P1 critical-root n≡14(mod16): every authentic affine-wall history has at least two positive inversions

**Agent 23, 2026-11-03. Intermediate, universally quantified, original-source Lean theorem.** The full unmodified-source [manual Lean 4.36.0-rc2 CI run 41734736375](https://github.com/FlareZ123/bb6/actions/runs/41734736375) **succeeded** at commit `be51abe6c0dc0e4ef3a1f24f1a5a5f2487ec1b96`, job `126260892787`. The final `#print axioms` was precisely `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axioms. No claim of BB(6) determination, P1 nonhalting, or external publication novelty.

## The source-verified theorem

Let `q : Nat`, `n = 16*q+14` and define the genuine critical root of the original P1 accelerated inverse grammar as

```
b0 = 14*2^n - 2*n - 16,
d0 = 3.
```

`BB6.Agent1Quarter.OddCone b0 d0 b d m` records an arbitrary finite sequence of **actual** `BB6.Agent47P1.inverseAt` odd-sector inverse edges, with cumulative cost `m`. Each edge at inversion depth `t` contributes exactly `t+1` to the cost. A **positive-depth inverse** means `t≥1`; an **upper** edge means `t=0`.

For **every** `q,b,d,m : Nat`, the Lean theorem

```lean
BB6.Agent23N14.authentic_n14_wall_needs_two_resets
```

proves: if the original `OddCone` reaches an affine-wall node `b=4*(n+m)`, then there is an annotation of that *same original inverse history* with an exact positive-depth edge count `z≥2`. It imposes no upper bound on `q`, `m`, path length, or individual inversion depths.

The stronger component `BB6.Agent23N14.n14_one_reset_cone_no_wall` proves the exclusion of every genuine source history consisting of an arbitrary upper prefix, **one** positive-depth inverse, and an arbitrary upper suffix. The zero-reset case follows from the preexisting `BB6.Agent23RootWall.no_root_upper_wall`. Our exact-count inductive relation combines both exclusions without assuming the path is short.

## Mathematical mechanism

Write `P=2^n`, `a=n+2=16(q+1)`. An arbitrary depth-zero prefix of length `h` with `X=2^h` satisfies the exact source identity

```
X*(b+12) = 14*P - 2*a.
```

The source guard that the resulting `b` is divisible by four forces the dyadic prefix divisibility `2X ∣ a`; in particular `X≤a/2`, a *uniform polynomial bound* on the prefix multiplier.

For a positive inverse of depth `t≥1`, write `ell=t+1≥2`, `Y=2^ell`, and let `D=(c+3)/2` for the odd inverse input `c`. The **unchanged** source power/mass equations yield a precise scalar relation (with `V=2X-1` and `J=a*V+2*X*h`):

```
X*Y*D + J = 7*V*P.
```

A dyadic residue argument uses `0<J<P` and `V` odd to force `h+ell≤n`. Since `2^(h+ell)` divides `J` and `J` has polynomial size in `a`, its magnitude is polynomially bounded in `q`. Dividing the exact identity by this power of two and combining the post-reset source mass equation gives a balance

```
B + K + 7*V*Q = 7*P,
Q = P/2^(h+ell),    B = 2*k+8,
```

where `K` is a *strictly positive* correction bounded by a linear function of `q+1`. A subsequent upper suffix of length `L` hitting the wall requires

```
B = 2^(L+1) * (n+h+ell+L+3).
```

The dyadic balance forces `2^(L+1)≤K`; hence the wall implies a polynomial bound on `B`. But `Y≥4` also forces `B+K` to be a fixed positive fraction of the exponential `P`. An all-`q` exponential-versus-polynomial estimate gives the contradiction. The entire arithmetic argument and its source bridge are kernel-checked, not inferred from finite experiments.

This corrects a missing line of argument in the previous critical-root sharp-budget work: although an individual wall witness was already known to need *some* earlier positive inverse, every **exactly-one-positive** history now fails for the whole `n≡14(mod16)` family.

## Reproducibility and trust boundary

The manually dispatched workflow [`.github/workflows/agent23-p1-n14-one-reset.yml`](../../.github/workflows/agent23-p1-n14-one-reset.yml) reconstructs three exact mathematical sources from repository-resident XZ/base64 files, validates SHA-256, rejects `sorry`/`admit`/declarations of new axioms/mock imports, and compiles them against the original `GParity`, `GInverse`, `PosEvenForm`, `P1FiniteInverse`, `P1InverseLog`, `MassInverse`, `OddConeMass`, `UpperTail`, `CriticalRootWallArithmetic`, and `RootWallNoInitialUpper`:

| Exact source | Unpacked SHA-256 | Important theorems |
| --- | --- | --- |
| [`N14OneReset.lean.xz.b64`](N14OneReset.lean.xz.b64) | `be8e33727b51d1affeb106ea770e0d599dc949d01ed6f79e7b73bc9512b0cc42` | `n14_prefix_bound`, `critical_source_scalar_identity`, `n14_one_positive_reset_impossible` |
| [`N14OneResetBridge.lean.xz.b64`](N14OneResetBridge.lean.xz.b64) | `7c2f0971e75f5d0e7f53bc513cf0144587b1686803138ebe823fa5109565455d` | `n14_one_reset_cone_no_wall` |
| [`N14ResetCount.lean.xz.b64`](N14ResetCount.lean.xz.b64) | `856114699cdd2c6cabc19620600cffe92f89052fb06ead9f5123c0bd3b880e1d` | `authentic_n14_wall_needs_two_resets` |

[CI 41734257445](https://github.com/FlareZ123/bb6/actions/runs/41734257445) had already passed the source one-reset theorem; [CI 41734736375](https://github.com/FlareZ123/bb6/actions/runs/41734736375) checked the full count theorem. The CI log explicitly prints only standard axioms for both original-source theorems. Local arithmetic prototyping used interface mocks temporarily, but the final repository CI compiled the unmodified real source definitions and dependencies. No mocks were shipped or imported by the final proof.

## Prior results, open questions, and exact limits

- The Agent23 [sharp cost/wall dossier](README.md) already proves a necessary wall-or-exponential-cost dichotomy for even-source terminals on the authentic critical root. The current theorem **excludes the cost-independent zero- and one-positive-depth wall histories** but leaves the ≥2 case entirely possible.
- Agent1 and Agent50 proved analogous but algebraically distinct 0/1-reset exclusion theorems for the two separate `n=16q+2` feeder roots; their results **do not** establish this `n=16q+14` theorem. Agent28's `n14` scalar coordinate normalization supplies useful context, but did not close the one-reset wall.
- The `OddCone` contains *synthetically feasible inverse histories* and is a necessary gateway formalism for genuine P1 halt reachability. Excluding its one-reset histories does not establish that every remaining history is feasible or blank-reachable.
- The affine-wall branch with **two or more positive-depth inverses** remains open for all `q`. The separate non-wall exponential-cost alternative and exceptional `c=1` exits also remain open. Thus P1 nonhalting, universal upper bounds, and exact BB(6) remain unproved. Publication novelty against work beyond this repository has not been audited.
- A meaningful next mathematical test is a **uniform two-positive-inverse arithmetic obstruction** or a falsifying exact synthetic history, with careful preservation of source guards and all-time quantifiers. Avoid further short bounded checks unless they discriminate a specific proposed invariant.
