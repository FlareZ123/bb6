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

## Universal fixed-index depth towers

The generic source-checked [`TowerAllOdd.lean`](TowerAllOdd.lean) advances any positive integer stopping index `m`, once it has a stopping-target certificate in one of the image-cylinder lattices with `2≤r` and `m≤r`. Let `P=2^(2*m+2)`, and let `(r,s,t)` describe the original source-certificate stopping target:

```
j=4*s+2*r+2,
k=2^r*(16*t+44)-2,
k+j+3*m+5=P*(j+3).
```

Define for every `h≥0`:

```
r_0=r,                 s_0=s,                       t_h=t,
r_(h+1)=r_h+2*m+2,
s_(h+1)=s_h+2^(r_h-2)*(16*t+44)-(m+1),
j_h=4*s_h+2*r_h+2,     k_h=2^r_h*(16*t+44)-2.
```

The source proof establishes, **without a finite depth or parameter bound**, that all `s_h` are nonnegative, that the exact high-stopping equation holds for every `j_h,k_h,m`, and that the authentic source blank section starting at `(5,1)` never reaches `(2*j_h+3,k_h)` at any time. Important inductive identities:

```
j_(h+1)=j_h+k_h+2 = P*j_h+(3*P-3*m-3),
k_(h+1)+2=P*(k_h+2).
```

The right-coordinate scaling preserves the cylinder's `t`; the new `s` guarantees its exact left coordinate with level `r+2*m+2`. The derivation uses Agent4's genuine source theorem, preserving original tape and seed semantics, and the source stopping identity, independently of any finite simulation horizon.

The exact source-derived `tower_stopping`, `tower_blank_excluded` and all-parameter instantiations `m1_tower_stopping`, `m1_tower_unreachable`, `m3_tower_stopping`, and `m3_tower_unreachable` **passed unchanged-original-source Lean CI [42610684885](https://github.com/FlareZ123/bb6/actions/runs/42610684885)** (standard axioms; no `sorryAx`). This lifts both table rows above to **three unbounded variables `a,q,h`**, with one source-certified stopping exclusion at every level `r=r_0+(2*m+2)*h`.

The enlarged families exclude **one residue progression in `j` per depth `h`**. Their progressions are pairwise disjoint: from `k_h+2=2^r_h*(16t+44)`, the valuation is exactly `v₂(k_h+2)=r_h+2`. For a fixed positive odd `m`, their asymptotic density in the `j` line is therefore (paper arithmetic, separate from the Lean reachability theorem):

| `m` class | Base depth `r_0` | Asymptotic density over `j` |
| --- | ---: | ---: |
| `m≡1 (mod4)` | `2*m` | `1/[4*(2^(2*m+2)-1)]` |
| `m≡3 (mod4)` | `2*m-1` | `1/[2*(2^(2*m+2)-1)]` |

For `m=1`, the first row contributes `1/60`; the independently certified earlier seed `j=256q+266` contributes another disjoint `1/240`, bringing the total to **`1/48`** as described above. For `m=3`, the second row alone gives **`1/510`**, before the three extra initial depth rays described below. These are conditional single-index-line densities; the countably many m-lines do not produce a positive two-dimensional density by themselves.

## Exact all-level coverage at `m=1` and `m=3`

Two source-connected, all-time, **all eligible depth** existence theorems now close the arithmetic image-cylinder intersection at the first two odd stopping indices:

- [`M1EveryEvenDepth.lean`](M1EveryEvenDepth.lean) proves for every even `r≥2` the existence of `s,t,j,k` with `j=4s+2r+2`, `k=bandY r t`, the authentic `m=1` stopping equation, and a proof that the blank section misses `(2j+3,k)` at all times. Source CI [42612465488](https://github.com/FlareZ123/bb6/actions/runs/42612465488), standard axioms.
- [`M3FourSeeds.lean`](M3FourSeeds.lean) proves three additional independent initial `m=3` stopping rays at `r=7,9,11`, plus each ray's full return-depth tower `r+8h`, source CI [42611850429](https://github.com/FlareZ123/bb6/actions/runs/42611850429). Together with `m=3,r=5+8h` from `GeneralM3.lean` and `TowerAllOdd.lean`, [`M3EveryOddDepth.lean`](M3EveryOddDepth.lean) proves for **every odd `r≥5`** that some authentic `m=3` stopping point at depth `r` is absent from every blank-section iterate. Source CI [42612271114](https://github.com/FlareZ123/bb6/actions/runs/42612271114), standard axioms.

The four `m=3` exact arithmetic rays, with `q,h≥0`, have base coordinates and positive progression steps:

| Initial `r` | Base `j(q)` | `s(q)` | `t(q)` | All tower depths |
| ---: | --- | --- | --- | --- |
| 5 | `372+512q` | `90+128q` | `184+255q` | `5+8h` |
| 7 | `244+2048q` | `57+512q` | `28+255q` | `7+8h` |
| 9 | `7924+8192q` | `1976+2048q` | `244+255q` | `9+8h` |
| 11 | `5876+32768q` | `1463+8192q` | `43+255q` | `11+8h` |

They are disjoint by exact valuation `v₂(k+2)=r+2`; for fixed `m=3`, the asymptotic `j`-line density is

```
(1/512 + 1/2048 + 1/8192 + 1/32768) / (1 - 1/256)
= 1/384.
```

The analogous complete even-depth `m=1` density is `1/48`. These cover **every eligible level** of the known Agent4 strict-image hierarchy at these two stopping indices. The source Lean theorems certify the exact equations, existential depth coverage, and all-time blank absence; the rational-density evaluations remain independently checkable paper arithmetic.

For arbitrary positive odd `m`, [`AllOddDepthArithmetic.md`](AllOddDepthArithmetic.md) derives a stronger uniform modular-inverse criterion at **every sufficiently deep parity-compatible image level**, with expected line densities `1/(3*2^(2m+2))` for `m≡1 mod4` and `2/(3*2^(2m+2))` for `m≡3 mod4`. This *uniform modular-existence step* remains to be kernel formalized. Its source-image premise and the all-index base towers are already certified.

### Earlier dyadic sieve and the unresolved frontier

At any strictly positive tower depth the source high-stopping equation and exact recurrence give

```
j_(h+1)+3*m+3=P*(j_h+3).
```

Thus for **every** allowed older dyadic inverse depth `n` with `n+4≤2*m+2`, the shifted stopping center reduces to zero modulo `2^(n+4)`, whereas that obstruction requires `2^(n+2)`. The theorem `tower_successor_misses_old_dyadic` proves this universally against the original source, [CI 42611085150](https://github.com/FlareZ123/bb6/actions/runs/42611085150). The `h=0` odd-index bases independently escape the old dyadic sieve by source-certified `GeneralM.lean` and `GeneralM3.lean`.

**Important limitation:** these genuinely new explicit all-parameter consequences of the existing image hierarchy have not yet been compared against the complete latest collection of source-proven high allowed restrictions or the full-forced nonreachability filter. A finite- or unbounded-depth root-connected classification remains necessary. The low-stopping family, other high parameters, Machine C blank halting, other six-state holdouts and exact BB(6) are **open**. This dossier belongs in `im-results/` pending independent novelty and strongest-sieve analysis.
