# Machine C: unbounded odd-index high-stopping exclusions from sharp image depth

**Status (9 November 2026): original-source Lean certified, conditional contribution to global BB(6).** The three modules [M1AllDepth.lean](M1AllDepth.lean), [GeneralM.lean](GeneralM.lean), and [GeneralM3.lean](GeneralM3.lean) prove all-time exclusions of explicit *authentic stopping targets* in the original Machine C first-return section. All compiled against unmodified source dependencies in selective manual Lean 4.36.0-rc2 [CI 42607003063](https://github.com/FlareZ123/bb6/actions/runs/42607003063), [CI 42607947984](https://github.com/FlareZ123/bb6/actions/runs/42607947984), and [CI 42609369597](https://github.com/FlareZ123/bb6/actions/runs/42609369597), respectively. [CI 42608160200](https://github.com/FlareZ123/bb6/actions/runs/42608160200) also certified the stronger prior-dyadic-escape theorem for the first all-index family. Printed axioms for the local stand-alone arithmetic are only `propext` and `Quot.sound`; the original-source builds include the imported source assumptions and contain no `sorryAx`.

## Exact research statement

Let `secNext` be the genuine, unmodified source first-return map of Machine C, with its authentic blank-derived seed `(5,1)`. The original high-stopping equation is

```
k + j + 3*m + 5 = 2^(2*m+2)*(j+3).
```

For **every** `a,q,time : Nat`, each of the following constructions satisfies that exact equation and the original blank section never reaches `(2*j+3,k)` at time `time`.

| Odd stopping index | High parameter `j` | Strict-image depth `r` |
| --- | --- | --- |
| `m=4*a+1` | `j=2^(8*a+4)*(4*q+2)-12*a-6` | `r=8*a+2=2*m` |
| `m=4*a+3` | `j=2^(8*a+7)*(4*q+3)-12*a-12` | `r=8*a+5=2*m-1` |

Here `k` is the canonical nonnegative high-stopping coordinate given by the equation. The three source-checked all-index theorems are `BB6.Agent19GeneralM.general_high_stopping`, `BB6.Agent19GeneralM.general_unreachable`, `BB6.Agent19GeneralM3.general_high_stopping`, and `BB6.Agent19GeneralM3.general_unreachable`. The corresponding `general_dyadic_not_excluded` theorems prove that **none of these target parameter pairs satisfies the earlier Agent 19 all-depth high dyadic obstruction at any allowed inverse depth**. This is a precise comparison to that earlier one sieve only; complete nonredundancy against the newest combined predicates and other full-forced or physical-root proofs is unestablished.

For the first row write `w=2^(8*a+2)`, `s=4*w*q+2*w-(7*a+3)`, and `t=4*w*q+2*w-(q+3*a+4)`. Lean proves `j=4*s+16*a+6` and `k=2^(8*a+2)*(16*t+44)-2`. For the second row write `w=2^(8*a+5)`, `s=w*(4*q+3)-(7*a+6)`, and `t=2*w*(4*q+3)-(q+6*a+8)`. Lean proves `j=4*s+4*(4*a+3)` and `k=2^(8*a+5)*(16*t+44)-2`. Nonnegativity of each explicit natural expression is proved, not assumed.

Agent 4's original-source [`CAllDepthBlank.lean`](../agent4-c-four-step-image/CAllDepthBlank.lean) already proves the **all-time seed exclusion** for any member of the exact cylinder

```
(x,y) = (8*s + 7 + 4*r, 2^r*(16*t+44)-2).
```

The novel work here is the all-parameter Diophantine intersection of this existing cylinder family with the source high-stopping equation. It does **not** claim a new section image inverse mechanism. Crucially, these are actual *necessary halting targets* that provably cannot be visited by the authentic blank orbit; generic unattainable prepared tapes alone would be insufficient for the intended application.

## The stronger `m=1` depth ladders

The first row at `a=0` is `j=64*q+26` and depth `r=2`, an existing result of Agent 4. A second independent Agent 4 seed is `j=256*q+266`, depth `r=4`. We extend both to **every depth offset `4*h`** with

```
A(q,0)=64*q+26,   A(q,h+1)=16*A(q,h)+42,
B(q,0)=256*q+266, B(q,h+1)=16*B(q,h)+42.
```

For all natural `h,q,time`, `(2*A+3,15*A+40)` and `(2*B+3,15*B+40)` are excluded. The closed image depth is `4*h+2` or `4*h+4`. Source Lean: `BB6.Agent19M1.ja_blank_unreachable` and `jb_blank_unreachable`, CI 42607003063. These ladders are pairwise disjoint across `h` and between A and B: the exact valuation of `15*j+42` is `4+4*h` for A and `6+4*h` for B. The asymptotic natural density **within the single line `m=1`** is

```
sum(h>=0, 1/(64*16^h) + 1/(256*16^h))
= 1/48.
```

The two original `h=0` seeds alone have density `5/256`; the new depths add `1/768` on that line. This density is a directly checked geometric-series calculation, not an independently kernel-certified density theorem. It is not a density across all `(j,m)` pairs. The much larger earlier joint sieve excludes other parameter families, and union masses cannot be summed without disjointness audits.

## Method, scope, and next mathematical problem

The useful common identity is the high stopping target's shifted coordinate `H_m(j)=k+2`. For fixed `m`, with `P=2^(2*m+2)` and `B=3*P-3*m-3`, one has

```
H_m(j)=(P-1)*j+B,
H_m(P*j+B)=P*H_m(j).
```

This suggests extending both all-index families into **an additional return-depth ladder** at fixed `m`, with `r` increasing by `2*m+2`, while the strict-image cylinder's `t` remains fixed. The underlying scalar algebra is elementary; a direct original-source Lean proof of all target-coordinate and nonnegativity side conditions has **not yet been checked**. A future proof should additionally audit whether the lifted families survive the latest global highAllowed and full-forced filters, and seek a finite or unbounded bound on *all* surviving high targets.

The remaining existential over `j,m`, the low-stopping family, the Machine C raw halting question, all other six-state holdouts, and BB(6) maximality remain **open**. This dossier belongs in `im-results/` pending full literature and strongest-prior-sieve novelty evaluation.
