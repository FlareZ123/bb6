# Machine C deep affine stopping inputs: exponential residual barrier

**Status, 6 November 2026:** The exponential theorem is **Lean 4.36.0-rc2 kernel certified against unchanged original Machine C source** in [CI 42210080956](https://github.com/FlareZ123/bb6/actions/runs/42210080956). The stronger uniform 220 lower wall, including exact low-index modular cases, is likewise source certified in [CI 42211050978](https://github.com/FlareZ123/bb6/actions/runs/42211050978). Both show only standard Lean axioms. These concern hypothetical stopping inputs; neither gives a Machine C halt/nonhalt proof or BB(6) exact value.

## Theorem

Let natural numbers `j,m,k,d,Y` satisfy

```
m >= 1, m odd,
k+j+3*m+5 = 2^(2*m+2) * (j+3),
2^d * (Y+2) = k+2.
```

Then

```
Y >= 2^(m+2) - 6*m - 1.
```

The statement is meaningful independently of the initial section's parity. For the source-certified *deep affine sector*, `Y` is precisely the genuine `BB6.Agent15.affineNormalize (2*j+3) k` residual right counter and `d=BB6.Agent15.oddDepth k`. In the genuine sector, existing `DeepSecondFinal.lean` also requires `Y>=4` and `Y%12=4`. For `m=3`, the new numeric lower bound is 13; it grows exponentially with odd `m`, in contrast to a fixed lower bound of 4.

This excludes residual right counter four for every odd `m>=3` under the exact stopping equation. The source-certified strengthening `odd_residual_ge_220` in [ResidualLowOdd.lean](ResidualLowOdd.lean) establishes **`Y>=220`** uniformly whenever `m>=3` is odd and `Y%12=4`. It checks the two exceptional small depths by finite modular arithmetic: `m=3` gives the exact lower limit 220 and `m=5` gives 508. For every odd `m>=7`, the now-certified exponential theorem implies at least 220. [ResidualSource.lean](ResidualSource.lean) composes these results with the original unbounded `affineNormalize`, `second_halt_deep_sector`, and `second_deep_affine_terminal_four_mod_twelve`. No result here settles blank-root reachability beyond the excluded region.

## Proof

Write `L=m+1`. Since `m` is odd, `L` is positive even. Set

```
B = (2^L-1)/3,  A = 2^L+1,  Q = A*B = (2^(2*L)-1)/3.
```

Here `B` is a positive odd integer, `2^L=3B+1`, and `m≤B<A`. To verify every size/parity assertion, write `m=2r+1` and `B_r=(2^(2r+2)-1)/3`. Direct algebra gives `B_0=1` and `B_(r+1)=4B_r+1`. Induction makes every `B_r` positive and odd; it also proves `B_r≥2r+1`, because `4B_r+1≥4(2r+1)+1≥2(r+1)+1`. Finally `A=3B+2>B≥m`.

From the stopping equation,

```
k+2 = (2^(2*L)-1)*(j+3) - 3*m.
```

Because `2^(2L)-1` is divisible by three, the scale equation implies `3 | 2^d*(Y+2)`. Since powers of two are coprime to three, write `Y+2=3*v` for a **positive** integer `v`. Dividing the stopping equation by three gives the exact equality

```
v*2^d + m = Q*(j+3).                (1)
```

It is enough to show `v+2*m > 2*B`. Suppose contrariwise `v+2*m <= 2*B`.

The identity `2^(2L) = 3Q+1` lets us replace `d` by the residue `t=d mod (2L)` when applying (1) modulo `Q`.

**Case `0 <= t < L`.** Since `v <= 2B-2m`,

```
0 < v*2^t+m <= (2B-2m)*2^(L-1)+m
             <= B*2^L+m < B*(2^L+1) = Q,
```

where the last strict inequality can be seen directly from `m<=B` (true for `m>=1` odd), with a stronger negative term in the preceding expression. This contradicts `Q | v*2^t+m`.

**Case `L <= t < 2L`.** Put `r=t-L`, so `0 <= r < L`, and `s=v*2^r`. Modulo `A`, the identity `2^L=A-1` gives `s ≡ m (mod A)`. Since `0 < m < A`, some integer `u>=0` satisfies

```
s = m+u*A.                          (2)
```

Modulo `B`, the identity `2^L=3B+1` gives `B | s+m = u*A+2m`, and `A=3B+2`, hence `B | 2*(u+m)`. As `B` is odd, `B | u+m`, which is a positive integer. Thus `u+m>=B`.

At the same time, (2) and `r<L` imply

```
u*2^L < m+u*A = s = v*2^r <= v*2^(L-1).
```

Therefore `2u<v`, and `v+2m>2(u+m)>=2B`, contrary to the assumption.

Both cases prove `v+2m>2B`. Since these are integers,

```
Y = 3*v-2 >= 3*(2B-2m+1)-2
            = 6B-6m+1
            = 2^(m+2)-6m-1.
```

This completes the paper proof.

## Arithmetic classification of the entire odd-m residual-four stopping locus

Combining the theorem with the verified `SecondOneInfinite.lean` tower gives a stronger **paper-level if-and-only-if** statement:

For every natural `j,m,k` with `m≥1` odd, satisfying the genuine second stopping equation, and with `Y` the exact Agent15 normalized right counter, `Y=4` **if and only if** `m=1` and `j=secondOneJ(r)` for some natural `r`, where `secondOneJ(0)=10` and `secondOneJ(r+1)=16*secondOneJ(r)+42`. In this case `k=15j+40` and the exact inverse depth is `d=4r+5`.

For necessity, first note that with m odd the stopping equation modulo two gives `k%2=j%2`. If `j` were odd, so would `k`; the original affine normalizer has no eligible first step and would terminate at `Y=k≥7` (Agent15's source-certified `second_halt_k_ge_seven`), contradicting `Y=4`. Thus `j` is even, the first coordinate is 3 modulo four, and Agent15's exact scale law applies. The exponential lower bound excludes `Y=4` whenever odd `m≥3`, since its right side is at least 13. Hence `m=1`. In the stopping equation, `k=15j+40`; the affine scale `2^d(4+2)=k+2` reduces to

```
5*j+14 = 2^(d+1).
```

Reducing modulo five, `2^(d+1)%5=4`. Powers of two have multiplicative order four modulo five, so `d+1=4r+2` for some `r≥0`; nonnegativity `j≥0` forces `d≥5` and hence `d=4r+5`. Substitution gives `j=(2^(4r+6)-14)/5`. This starts at 10 and obeys `j(r+1)=16j(r)+42`. Sufficiency and source-exact inverse depth for every such `r` are already established in `SecondOneInfinite.lean` by the authentic affine normalizer, and the stopping relation is directly certified.

**Evidence:** The sufficiency direction, recurrence, stopping equation and blank-root exclusion are Lean source certified. The all-odd-m **necessity** uses the above new exponential paper theorem, which still needs a complete Lean translation. Do not treat the if-and-only-if itself as kernel certified.

## Source chain, reproducibility and limits

The exact second-family equation is the original Machine C stopping identity in `im-results/agent15-c-halting/`. The affine-scale equation `2^d(Y+2)=k+2` is `normalize_three_depth_invariants` in `AffineParityDepth.lean`, imported by `second_halt_deep_sector` in `SecondDeepSector.lean`. The factor-three lemma and genuine residual `Y%12=4` are in `ModThree.lean` and `DeepSecondFinal.lean`. New [ResidualPeriod.lean](ResidualPeriod.lean), [ResidualCore.lean](ResidualCore.lean), [ResidualExponential.lean](ResidualExponential.lean), [ResidualLowOdd.lean](ResidualLowOdd.lean), and [ResidualSource.lean](ResidualSource.lean) close the entire proof chain. Unchanged-source CI runs [42210080956](https://github.com/FlareZ123/bb6/actions/runs/42210080956) and [42211050978](https://github.com/FlareZ123/bb6/actions/runs/42211050978) both succeeded. The final source-linked theorem is `BB6.Agent29Barrier.second_deep_affine_residual_ge_220`.

Finite checks at even `j` with `(j+m)%4=3`, `m=1,3,5,7,9,11`, and `j<200000` found minima `4,220,508,45052,327676,16252924`. The `m=3,5` lower limits are now Lean theorems for all indices and inverse depths; the other finite entries are listed as paper-level findings in [OddDepthExactModularMinimum.md](OddDepthExactModularMinimum.md). The exponential and uniform-220 theorems quantify over arbitrary natural stopping parameters and inverse depths.

The next valuable application is to combine this depth-dependent obstruction with exact source inverse ancestors of the surviving residuals. It remains unknown whether any stopping input is reached from the authentic blank section at all.
