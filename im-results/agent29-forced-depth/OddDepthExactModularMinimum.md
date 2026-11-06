# Exact finite modular minimization for odd-depth Machine C high stopping residuals

**Status (6 November 2026):** An exact number-theoretic reduction with elementary proof and reproducible Python arithmetic, **not a Lean-certified composite theorem**. It quantifies over the source-certified original high stopping and affine-scale equations. No original blank-reachability conclusion is asserted here.

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
