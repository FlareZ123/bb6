# Exact finite modular minimization for odd-depth Machine C high stopping residuals

**Status (21 November 2026):** The exact finite modular minimization and the uniform sharp envelope below have elementary proofs. The new envelope and its infinite source-normalized sharpness composition are **not yet Lean-certified**. They quantify over the source-certified original high stopping and affine-scale equations; no blank-root reachability conclusion is asserted.

Let m≥1 be odd, j,k,d,Y natural, and suppose

```
k+j+3*m+5 = 2^(2*m+2)*(j+3),
2^d*(Y+2) = k+2,
Y%12 = 4.
```

Set L=m+1 (even), Q=(2^(2*L)-1)/3 (odd), T=2*L. For each integer t in [0,T), define

```
r_t = (-m * inverse_mod(2^t,Q)) mod Q,  0<=r_t<Q,
v_t = r_t + ((2-r_t) mod 4)*Q.
```

The modular inverse exists because Q is odd, and Q≡1 mod4 because L≥2. No v_t can be zero: v_t≡2 mod4. Then **the following is a rigorous universal necessary bound**:

```
Y >= min_(0<=t<T) (3*v_t-2).                      (★)
```

The RHS is computable from m using **exactly T=2m+2 modular operations**, independent of j,k,d and their magnitudes. It is the smallest nonnegative right counter compatible with these *necessary modular conditions*. Further source equations could rule out even that minimum; (★) does not guarantee genuine blank reachability or original stopping-state ancestry.

## Proof

From the high stopping equation, `k+2=(2^(2L)-1)*(j+3)-3m=3(Q*(j+3)-m)`. As `2^d` is coprime to three, the scale equation forces `3|(Y+2)`; since `Y≡4(mod12)`, write `Y+2=3v` for v>0 with v≡2(mod4). Dividing the scale identity by 3 yields

```
v*2^d + m = Q*(j+3).
```

In particular `v*2^d≡-m(modQ)`. Since `2^T=2^(2L)=3Q+1`, powers of two mod Q have period dividing T, so t=d modT satisfies `v≡-m(2^t)^(-1)(modQ)`. This is `v≡r_t(modQ)`. Because Q≡1(mod4), all simultaneous solutions of `v≡r_t(modQ)` and `v≡2(mod4)` are `v=v_t+4Qh` for integers h. Their least positive nonnegative representative is the displayed v_t. Thus v≥v_t for the actual t, whence Y=3v-2≥3v_t-2≥min_t(3v_t-2). All steps use exact arithmetic; no dynamic simulation.

## Uniform envelope and infinite sharpness

The finite minimum (★) has a simple uniform lower envelope. Under the same hypotheses,

```
(3*m+1)*(Y+2) >= 2^(2*m+3) - 6*m - 2.
```

Equivalently, with `Q=(2^(2*m+2)-1)/3` and `v=(Y+2)/3`,

```
v >= 2*(Q-m)/(3*m+1),
Y >= 3*ceil(2*(Q-m)/(3*m+1))-2.
```

This is a `4^m/m`-scale lower bound, stronger than the previously source-certified `2^(m+2)-6*m-1` bound throughout the odd positive range. It is still a necessary condition on the normalized residual, not a blank-root decision.

### Proof of the envelope

Put `L=m+1`, `Q=(2^(2*L)-1)/3`, and `Y+2=3*v`. The last identity and `Y%12=4` give `v%4=2`. The stopping equation and affine scale give

```
v*2^d + m = Q*(j+3),       2^(2*L)=3*Q+1.
```

Reduce `d` modulo `2*L`, writing `t=d%(2*L)`. Then `Q | v*2^t+m`; set `n=(v*2^t+m)/Q`. For `t<=2*L-2`, the congruence `v%4=2` gives

```
n*Q = v*2^t+m = m+2^(t+1)  (mod 2^(t+2)).
```

Since `3*Q=2^(2*L)-1`, the inverse of `Q` modulo `2^(t+2)` is `-3`. Hence

```
n = 2^(t+1)-3*m  (mod 2^(t+2)).
```

If `2^(t+1)<=3*m+1`, use `n>=1` to obtain `v>=(Q-m)/2^t >= 2*(Q-m)/(3*m+1)`. Otherwise `2^(t+1)-3*m` is the least positive residue, so

```
v >= ((2^(t+1)-3*m)*Q-m)/2^t
  = 2*Q-(3*m*Q+m)/2^t
  > 2*(Q-m)/(3*m+1),
```

where the final inequality uses `2^t>(3*m+1)/2`.

For the remaining residue `t=2*L-1`, let `A=2^(2*L)`. Here `n` is odd, and reduction modulo `2*A` in `n*(A-1)=3*(v*2^(2*L-1)+m)` gives `n=-3*m (mod 2*A)`. Since `0<3*m<2*A`, `n>=2*A-3*m`; substituting in `v=(n*Q-m)/(A/2)` gives `v>Q`, which is stronger than the claimed bound. Multiplying the bound for `v` by three and substituting `Q=(2^(2*L)-1)/3` proves the displayed inequality.

### The envelope is sharp for infinitely many genuine source-normalized inputs

For every `r>=1`, take

```
m=(4^r-1)/3,   t=2*r-1,   L=m+1,   Q=(2^(2*L)-1)/3,
v=(Q-m)/2^t,   d=t+2*L,
j=3*v*2^t-2,  k=3*v*2^d-2,  Y=3*v-2.
```

Because `3*m+1=2^(t+1)` and `t+2<=2*L`, the identity `3*Q=2^(2*L)-1` gives `Q-m=2^(t+1) (mod 2^(t+2))`. Thus `v` is an integer with `v%4=2`. Also `m%4=1`, `j%4=2`, so `j` is even and `(j+m)%4=3`. Direct substitution using `v*2^t=Q-m` and `2^(2*L)=3*Q+1` verifies both the original second stopping equation and `2^d*(Y+2)=k+2`.

These parameters therefore lie in the exact deep sector of the original source. The already source-certified `second_halt_deep_sector` and `second_deep_affine_terminal_four_mod_twelve` give the actual unbounded `affineNormalize` output with right residual congruent to four modulo twelve and the same scale identity. Since `k+2=3*v*2^d` has 2-adic valuation `d+1`, while every such source residual plus two has 2-adic valuation one, that source normalization must have depth `d` and residual exactly `Y`. The displayed envelope is therefore attained by genuine source-normalized stopping inputs for infinitely many odd `m` (not merely by abstract modular representatives). This final source-normalizer identification is a paper composition here, not a new Lean theorem.

The first two instances are:

| `r` | `m` | `j` | `k` | normalized `Y` |
|---:|---:|---:|---:|---:|
| 1 | 1 | 10 | 190 | 4 |
| 2 | 5 | 4,078 | 16,711,678 | 508 |

The `r=1` case is the existing right-four tower; `r=2` shows that the exact `m=5` lower bound 508 is attained at an actual source-normalized stopping input. Neither example is asserted to be blank-reachable.

### Relation to the exact finite minimum

The finite minimizer (★) remains sharper for many individual `m`; the new envelope is a closed-form bound valid uniformly for every odd `m` and is exactly sharp on the infinite sequence above. For the sample values already tabulated, its lower bounds on `Y` are 4, 49, 508, 5,956, 74,896, 986,893, and 13,421,770 for `m=1,3,5,7,9,11,13`, respectively. The exact finite minima remain 4, 220, 508, 45,052, 327,676, 16,252,924, and 67,108,852.

## Reproducible exact minimization

The following Python 3 code uses the built-in modular inverse and arbitrary-precision integers. It enumerates all t for each fixed m and returns the sharp necessary modular bound and attaining exponent residue.

```python
def lower_bound(m: int) -> tuple[int, int]:
    assert m >= 1 and m % 2 == 1
    L = m + 1
    Q = (2 ** (2 * L) - 1) // 3
    candidates = []
    for t in range(2 * L):
        r = (-m * pow(2 ** t, -1, Q)) % Q
        v = r + ((2 - r) % 4) * Q
        candidates.append((3 * v - 2, t))
    return min(candidates)

for m in (1, 3, 5, 7, 9, 11, 13):
    print(m, lower_bound(m))
```

Output recomputed in the local Python runtime:

| odd m | necessary minimum Y | exponent residue d mod (2m+2) |
| ---: | ---: | ---: |
| 1 | 4 | 1 |
| 3 | 220 | 3 |
| 5 | 508 | 3 |
| 7 | 45052 | 4 |
| 9 | 327676 | 4 |
| 11 | 16252924 | 5 |
| 13 | 67108852 | 2 |

For m=1, the genuine source-certified tower [SecondOneInfinite.lean](SecondOneInfinite.lean) has d=4r+5 and terminal Y=4; d≡1(mod4), matching the exact minimization. For m=3,5,7 the displayed minimum also appears among actual (though **not necessarily blank-reachable**) stopping inputs in exploratory exact source-normalization computations. Those observations do not replace the universal modular proof.

## Relevance and limitations

This refines the independent paper proof [DeepResidualExponentialBarrier.md](DeepResidualExponentialBarrier.md), which gives a simple uniform analytic bound `Y≥2^(m+2)-6m-1`. The new finite minimizer often gives much stronger per-m restrictions and can be evaluated without enumerating huge j or k. It specializes to the source-certified deep affine stopping-sector terminal property `Y%12=4` in [DeepSecondFinal.lean](DeepSecondFinal.lean), whose original-source proofs were checked by [CI 42196589496](https://github.com/FlareZ123/bb6/actions/runs/42196589496).

The global Machine C halting/blank reachability question remains open, and no claim here determines BB(6). Strong next work: formalize (★) in Lean against exact original sources and combine the finite set of surviving residue representatives with source-exact backward reachability certificates.
