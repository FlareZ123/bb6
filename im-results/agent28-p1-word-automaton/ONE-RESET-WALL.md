# P1 critical n≡14 (mod 16): an all-parameter zero/one-reset wall obstruction

**2026-11-04, Agent 28. Full original-source Lean proof for every n≥30, with separate hand-checked finite n=14 arithmetic.** The complete n≥30 counted result was verified against unmodified `inverseAt`, `OddCone` and `UpperTail` source in [GitHub Actions run 41747347637](https://github.com/FlareZ123/bb6/actions/runs/41747347637), job 126303562909, **success** under Lean 4.36.0-rc2. This restricts possible inverse histories and does not establish P1 nonhalting or BB(6).

## Statement

Let `n=16q+14` for arbitrary `q:Nat`, put `P=2^n`, `K=7P-n-3`, and initialize the normalized critical odd inverse cone at `(D,m)=(1,0)`. Its odd predecessor transitions, as in the already authenticated [Agent28 scalar source bridge](README.md), have `l=t+1≥1` and

```
2^l D' = K + D - m,       m' = m + l,
E = K-D-m,                b = 2E-8.
```

Retain only transitions satisfying the source's integrality, positivity and predecessor guards. Call a transition a **reset** if `l≥2` (equivalently original inverse depth `t≥1`), and an **upper** transition if `l=1` (`t=0`).

**Claim:** No admissible finite history starting at `(1,0)` containing **zero or exactly one reset** ends on the affine wall

```
b=4(m+n), equivalently E=2(m+n)+4.
```

This is an all-q obstruction for the `n≡14 (mod16)` critical cone, complementary to Agent50's source-certified zero/one-reset obstruction on two `n≡2 (mod16)` feeders. The source-level theorem `BB6.Agent28.source_critical_wall_needs_two_resets` is now verified for every n≥30. Its `CountCone` annotation faithfully records every genuine `inverseAt` positive-depth transition. The finite n=14 calculation below is an independent arithmetic check and is not included in that source theorem.

## Derivation for n≥30

Write `R=2^r` for an initial run of `r` upper transitions. The recurrence `E'+2=(E+2)/2` gives

```
R(E_r+2)=B,   B=K+1=7P-(n+2).
```

Since `0<n+2<2^n` and `R|B`, we have `r<n`, `R|(n+2)`, `R≤n+2`, and `r≤n+1`. Define `u=(n+2)/R` and the positive integer

```
M=2(n+r+2)-u,    0<M<4(n+2).
```

The numerator for the single reset of length `l≥2` is

```
T=K+D_r-r=2(K-r+1)-B/R
 =7(P/R)(2R-1)-M.
```

Its exact integrality requirement is `L=2^l | T`. The elementary growth bound `4(n+2)^2<P` implies `0<M<P/R`. The first term of `T` is an **odd multiple** of the power of two `P/R`, hence `v₂(T)=v₂(M)`. Consequently `L|M`, `L≤M<4(n+2)`, and `RL|P`.

The reset output is `D_*=T/L`. Its shifted left coordinate satisfies the **exact identity**

```
E_*+2=7(P/(RL)) C-N,
C=RL-2R+1  (positive odd),
N=n+r+l+1-M/L.
```

Because `l≥2`, `0<N<6(n+2)`; also

```
RLN < 24(n+2)^3 < P.
```

Thus `0<N<P/(RL)`, and the same 2-adic argument shows that any subsequent run of `s` uppers has `S=2^s | N`, whence `S≤N<6(n+2)`. Its total inverse cost is `m=r+l+s≤R+L+S<11(n+2)`.

On the putative wall, `E_f+2=2(m+n+3)`. But the exact upper recurrence implies `E_*+2=S(E_f+2)`. Hence

```
7PC = RL [ N + 2S(m+n+3) ].
```

With `C≥1`, and all the bounds just established,

```
7P ≤7PC
   ≤ RL·N·[1+2(m+n+3)]
   <24(n+2)^3·[24(n+2)+3]
   <7P,                                  CONTRADICTION.
```

The final growth inequality holds for every `n≥30`. At `n=30`, the right polynomial equals `606339072`, strictly below `7·2^30=7516192768`. For `x=n+2≥32`, both factors `x` and `24x+3` grow by at most `33/32` per increment; `33^4<2·32^4` proves the inductive growth comparison. The same final inequality immediately implies `4(n+2)^2<P` and `24(n+2)^3<P`.

For **zero resets**, the root upper recurrence and wall would give `7P=(n+2)+2R(r+n+3)`, but `R≤n+2`, `r≤n+1` bound the right side by `(n+2)[1+4(n+2)]<7P` for `n≥14`.

## Exceptional smallest exponent n=14

Here `K=114671`, `B=114672`, `v₂(B)=4`; thus only `0≤r≤4` can begin a reset. Exhausting the *relaxed* exact integrality rules (even allowing branches that other source guards may reject) gives:

| r | Reset lengths l≥2 allowed by L∣T | Maximum possible upper suffix s |
|---|---|---|
| 0 | 2,3,4 | 4 |
| 1 | none | — |
| 2 | 2,3,4,5 | 4 |
| 3 | 2 | 0 |
| 4 | none | — |

The possible `E_*+2` are `86003,100336,107502,64501,89584,102125,108395,60917`. Therefore `E_*+2≥60917`, `S≤16`, `m=r+l+s≤13`, and any terminal `E_f+2≥60917/16>3800`. The wall would force `E_f+2=2(m+17)≤60`, impossible. Without a reset, `E_r+2=B/R≥7167` while the wall demands at most 42.

## Verification and remaining scope

- `OneResetGrowth.lean`, `OneResetTwoAdic.lean`, `OneResetBudget.lean`, `OneResetSourceEq.lean`, `OneResetPoly.lean`, and `OneResetSourceBudget.lean` establish the all-n≥30 uniform dyadic cancellation and wall contradiction. The original `UpperTail` source bridge `OneResetSourceBridge.lean` passed [full-source CI 41747017916](https://github.com/FlareZ123/bb6/actions/runs/41747017916). `OneResetZero.lean` and `OneResetCount.lean` establish the combined count≥2 theorem, original-source [CI 41747347637](https://github.com/FlareZ123/bb6/actions/runs/41747347637) **success**. No new axioms or sorry are introduced.
- Algebraic formulas were independently checked by exact-integer recurrence enumerations, including `n=14,30,46,62,78,94,110,126,142,158,190,254,286,526,750,1006,2046,4094` under the displayed relaxed guards. These finite checks are corroboration only.
- All operations on the actual `OddCone` must retain the original `inverseAt` integrality and output conditions. The proof safely overapproximates by omitting additional guards; it never infers original blank reachability from synthetic predecessor feasibility.
- The result eliminates one **specific low-cost affine-wall mechanism** for the `n≡14` critical family. It does not eliminate two-or-more resets, high-cost positive-even exits, the exceptional `c=1` exit, other exponents, or the P1 machine overall.

**Next work:** use the exact generic defect recurrence in [DefectTransport.lean](DefectTransport.lean) and [MULTIRESET-DEFECT.md](MULTIRESET-DEFECT.md) to obtain a parameter-uniform lower bound on the number of resets needed by any possible wall history, then address high-cost and exceptional even exits. The n=14 enumeration may be formalized separately; Agent47's original-source n≡14(mod1024) critical-gateway exclusion is existing related work. Seek independent novelty and correctness review before moving any intermediate findings into `results/`.
