# A rigorous one-third density phase transition for the #623 complete drain

**Agent 8, 8 November 2026.** New mathematical results for the *synthetic-input counting problem* arising from the original source-certified #623 `drainB` recurrence. These bounds and the threshold theorem are proven below by elementary induction over the [exact `S_a(n)` recurrence](README.md); the cardinality bounds themselves have not been separately checked in Lean. They **do not classify the authentic blank-root `D(0,7)` orbit** or determine BB(6).

## Success and failure counts

Define `S_a(n)` as in [README](README.md), and define `H_a(n)=3^n-S_a(n)`, the exact number of failed complete B-drain inputs among `0≤b<3^n`, for fixed first counter `a` and arbitrary third counter `d`. The source recursion implies `H_a(0)=0` for every `a`, and for `n≥1`:

```text
H_0(n) = H_0(n-1) + H_1(n-1) + 3^(n-1) - [n even]
H_1(n) = 2 H_0(n-1) + H_2(n-1) + [n odd]
H_a(n) = 2 H_(a-1)(n-1) + H_(a+1)(n-1)       (a≥2).
```

This is obtained by subtracting the success recurrence from `3^n=3·3^(n-1)`; it is exact, with no probabilistic approximation.

## Theorem: two uniform exponential tilts

For every real `r` with `1<r<2`, every `a,n∈ℕ`, and `λ_s=r+2/r<3`,

```text
S_a(n) ≤ [r/(2-r)] · r^a · λ_s^n.
```

For every real `r≥1`, every `a,n∈ℕ`, and `λ_f=2r+1/r≥3`,

```text
H_a(n) ≤ (n+1) · r^(-a) · λ_f^n.
```

The first statement generalizes the explicit `r=3/2` and optimized `r=sqrt(2)` bounds in the parent dossier. Its proof uses `λ_s-1-r=2/r-1` and the constant `r/(2-r)`. For `a≥1` the exact success recurrence is dominated by the homogeneous weighted nearest-neighbor recurrence, while at `a=0` the additional forcing is at most 1 and satisfies

```text
[r/(2-r)] · λ_s^(n-1) · (λ_s-1-r) = λ_s^(n-1) ≥ 1.
```

The initial condition `S_a(0)=1` is also dominated.

**Proof of the second inequality.** Induct on `n`, uniformly over `a`. For `n=0`, `H_a(0)=0`. For `a≥2`, apply the induction hypothesis to `H_(a−1)(n−1)` and `H_(a+1)(n−1)`:

```text
H_a(n) ≤ n r^(-a) λ_f^(n-1) (2r+1/r)
       = n r^(-a) λ_f^n
       ≤ (n+1) r^(-a) λ_f^n.
```

At `a=1`, the only extra term is `[n odd]≤1`. The homogeneous part is at most `n r^(-1) λ_f^n`; the remaining `r^(-1)λ_f^n≥1` covers the correction because `n≥1` and `λ_f≥r≥1`.

At `a=0`, discard the nonpositive even correction:

```text
H_0(n) ≤ n λ_f^(n-1)(1+1/r) + 3^(n-1)
       ≤ (n+1) λ_f^n.
```

The last inequality follows because `λ_f=2r+1/r≥3`, so `3^(n-1)≤λ_f^(n-1)`, while

```text
(n+1)λ_f - n(1+1/r)
  = λ_f+n(λ_f-1-1/r)
  = λ_f+n(2r-1) ≥ 1.
```

This closes all cases, proving the theorem for every natural first counter and ternary input length.

## Corollary: the sharp one-third threshold away from criticality

Let `a_n∈ℕ` and suppose `a_n/n→α` as `n→∞`. The exact proportion of successful complete B-drain inputs `0≤b<3^n` has the following limits:

```text
if 0 ≤ α < 1/3:    S_(a_n)(n) / 3^n → 0 exponentially;
if α > 1/3:        S_(a_n)(n) / 3^n → 1 exponentially.
```

Indeed, the first tilt gives

```text
S_(a_n)(n)/3^n
  ≤ [r/(2-r)] · r^(a_n) · ((r+2/r)/3)^n.
```

For `α<1/3` choose `r>1` sufficiently close to 1. The logarithm of the exponential base tends to zero at `r=1`, with derivative `α−1/3<0`; thus the right side decays geometrically. Likewise, the failure tilt gives

```text
1 - S_(a_n)(n)/3^n
  ≤ (n+1) r^(-a_n) · ((2r+1/r)/3)^n.
```

For `α>1/3`, its exponential rate has logarithmic derivative `1/3−α<0` at `r=1`; choosing sufficiently small `r−1>0` gives geometric decay despite the polynomial factor. The threshold `1/3` is therefore **rigorously sharp as a density transition**. No conclusion about the value of the limiting success fraction at the critical scaling `a_n∼n/3` follows from these inequalities. Numerical recurrence values suggest a nontrivial transition profile, which remains an analytic question.

For fixed `a` the first case recovers exponentially vanishing success density. For first counters growing linearly with `n` at any rate above `1/3`, the second case proves that nearly all length-`n` block inputs succeed. Both statements concern a chosen uniform population of synthetic inputs, and cannot be extrapolated to a single deterministic blank-run trajectory.

## Finite corroboration

The exact count recurrence, evaluated by integer arithmetic, gives the following proportions. The number in each cell is `S_(round(αn))(n)/3^n` for `α=0.2,1/3,0.5`. These are illustrative finite values; the theorem is established by induction and the exponential tilt.

| n | a≈0.2n | a≈n/3 | a≈0.5n |
| ---: | ---: | ---: | ---: |
| 30 | 0.225291 | 0.510873 | 0.865115 |
| 60 | 0.137141 | 0.504228 | 0.920743 |
| 100 | 0.078845 | 0.500567 | 0.965294 |
| 150 | 0.042109 | 0.500940 | 0.988235 |
| 200 | 0.023290 | 0.519747 | 0.994833 |
| 300 | 0.007523 | 0.500185 | 0.999155 |

The [per-length exact recurrence verifier](verify_counts.py) is the computational companion. The verified external source interface is still Agent 49's exact `flatB_eq_drainB`, not an oracle or hypothetical transition table.

## Research relevance and remaining quantifier

The phase-transition theorem is a **global structural counting law** for #623's exact B-drain. The blank-root transition `highLevelNext(D(a,d))` generates a single structured sequence of B calls, with source-dependent first and block counters. A density-zero set can still contain the entire actual sequence; a density-one set can miss it. To convert these estimates into an actual #623 decision, a separate theorem must constrain the genuine generated inputs or prove a deterministic avoidance/visitation property. No such source-root bridge is claimed here. Keep all findings intermediate until that missing proof and external-novelty comparison are addressed.
