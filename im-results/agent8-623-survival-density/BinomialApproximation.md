# Uniform binomial approximation and Gaussian critical window for #623 B-drain

**Paper theorem, 8 November 2026.** This note derives a *uniform-in-the-first-counter* quantitative approximation for the original source-shaped complete B-drain from the source-certified exact ternary recursion and the new exact count bound in [README.md](README.md). The probability is the uniform **enumeration** of all `b<3^n`, not a stochastic interpretation of the true deterministic machine. This analytic theorem is not yet Lean formalized. It **does not decide** the authentic blank-root `D(0,7)` orbit or BB(6).

## Theorem

For each `a,n≥0`, write

```text
p_a(n) = #{0≤b<3^n : drainB(a,b,d) succeeds} / 3^n
       = S_a(n) / 3^n,
```

independently of `d`. Let `K_n ~ Binomial(n,1/3)`. There is an **absolute** constant `C` such that for every `n≥1`, uniformly over all `a≥0`,

```text
| p_a(n) - Pr( a + 2*K_n - n > 0 ) | ≤ C / sqrt(n).
```

By the classical Berry–Esseen bound for Bernoulli sums, the equivalent uniform normal approximation is

```text
sup_{a≥0} | p_a(n) - Φ((3*a-n)/(2*sqrt(2*n))) |
    = O(1/sqrt(n)),
```

where `Φ` is the standard normal cumulative distribution function. In particular, for every fixed real `x` and any integer sequence `a_n=n/3+x*sqrt(n)+o(sqrt(n))`,

```text
p_(a_n)(n) → Φ(3*x/(2*sqrt(2))).
```

This resolves the **critical one-third density window** left open by the exponential two-sided estimates in [PhaseTransition.md](PhaseTransition.md). For example, if `a_n` is any nearest integer to `n/3`, then exactly half of all ternary length-`n` block inputs succeed asymptotically. This remains a synthetic-input distributional result.

## Proof: a coupled biased random walk

Take `b` uniformly from `{0,1,...,3^n-1}` and write its independent ternary digits as `b=∑_(i=0)^(n-1) x_i 3^i`, with each `x_i` uniform on `{0,1,2}`.

The source-complete drain recursion is summarized in [README.md](README.md). Before the drain stops, after `i` recursive calls its remaining block argument can be expressed as

```text
b_i = floor(b/3^i) + c_i,     -1 ≤ c_i ≤ 1,    c_0=0.
```

Indeed, given `b_i>0`, let `r_i=b_i mod 3`, `q_i=floor(b_i/3)`, and let `t_i=floor((x_i+c_i)/3)` use Euclidean floor (valid when `x_i+c_i=-1`). The exact source update is

```text
b_(i+1) = q_i+s_i,
s_i = -1 if r_i=0,
        0 if r_i=1, or if r_i=2 and a_i=0,
       +1 if r_i=2 and a_i>0.
c_(i+1) = t_i+s_i.
```

The carry interval is invariant, case by case: `r_i=0` gives `c_(i+1)∈{-1,0}`; `r_i=1` gives 0; `r_i=2` gives `{-1,0}` when `a_i=0` or `{0,1}` when `a_i>0`. Moreover `r_i=(x_i+c_i) mod 3`. Conditional on the lower `i` digits, `c_i` is fixed, so `r_i` is still uniform on three residues. Therefore, up to first contact with first counter zero, the first counter is an ordinary random walk with independent increments

```text
Y_i = +1 if r_i=0, otherwise -1,
Pr(Y_i=+1)=1/3, Pr(Y_i=-1)=2/3.
X_0=a, X_t=a+Y_0+...+Y_(t-1).
τ = inf{t≥0 : X_t=0}.
```

After `τ`, extend the residues with independent fresh ternary digits if necessary; only the pre-`τ` coupling matters. For `a≥1`, until `τ` or an earlier successful `b_i=0` exit, the actual drain first counter equals `X_i`. At time `n`, any still-active residual block must be `b_n=1`, since `floor(b/3^n)=0` and `c_n∈{-1,0,1}`. From positive first counter, the residual `b_n=1` succeeds in one last source step. Hence

```text
Pr(τ>n) ≤ p_a(n).
```

This also holds for `a=0` with a zero left side.

## Proof: control the two ways to succeed after a walk hits zero

Put `ρ=17/18<1`. The exact global counting theorem gives `S_0(m)/3^m≤3ρ^m` for every `m`. For any fixed carry `c∈{-1,0,1}`, with an independent uniform `U∈{0,...,3^m-1}`, shifting the B-input by c alters the number of successful inputs by at most one boundary value. If `U+c<0`, count this single inadmissible value pessimistically. Thus

```text
Pr(drainB(0,U+c,d) succeeds, with negative arguments discarded)
    ≤ (S_0(m)+1)/3^m ≤ 4ρ^m.
```

A separate elementary local-binomial bound gives, uniformly over any starting `a` and any integer `j`, for `t≥1`,

```text
Pr(X_t=j) ≤ C_0/sqrt(t),
```

for some universal `C_0`, since `X_t=a+2K_t-t`. The `Y_i` also satisfy a geometric positive-tail bound:

```text
Pr(Y_1+...+Y_m>0)
 ≤ E[(sqrt(2))^(Y_1+...+Y_m)]
 = (2sqrt(2)/3)^m.
```

We now partition a successful drain with `τ≤n` according to its first successful exit.

**Case I: the drain stopped at a zero block strictly before `τ`.** Suppose the zero-block exit is at time `i<τ≤n`, and write `m=n-i`. As `X_i>0` and there are only `m` possible future negative increments, necessarily `1≤X_i≤m`. Conditional on the lower `i` ternary digits, the equation `b_i=0` forces a *single* possible choice of upper block `U=floor(b/3^i)=-c_i`, which has probability at most `3^(-m)`. Hence, by a union bound over possible `i`,

```text
Pr(Case I) ≤ ∑_(i=0)^(n-1) 3^(-(n-i)) Pr(1≤X_i≤n-i).
```

For `i≤n/2`, this is `O(n 3^(-n/2))`). For `i>n/2`, use the local-binomial bound on at most `m=n-i` possible counter values: `Pr(1≤X_i≤m)≤C_0 m/sqrt(i)`. The sum is bounded by `(O(1)/sqrt(n))∑_(m≥1)m/3^m=O(n^(-1/2))`.

**Case II: the drain is still active when `τ=t≤n` first reaches zero.** Conditional on the first `t` lower digits, the future upper block `U=floor(b/3^t)` is uniform on `0..3^(n-t)-1`, and the current block is `U+c_t` for fixed `c_t∈{-1,0,1}`. The success chance is at most `4ρ^(n-t)`, by the fixed-zero-counter counting bound. Consequently

```text
Pr(Case II) ≤ 4∑_(t=0)^n Pr(τ=t) ρ^(n-t).
```

For `t≤n/2`, this is at most `4ρ^(n/2)`. For `t>n/2`, `τ=t` implies `X_t=0`, so the local-binomial bound gives `Pr(τ=t)≤C_0/sqrt(t)`. Summing the geometric tail yields `O(n^(-1/2))`. Combining both cases,

```text
0 ≤ p_a(n) - Pr(τ>n) = O(n^(-1/2)),
```

uniformly in the starting first counter `a`.

## Proof: replace first passage by the binomial endpoint

Certainly `τ>n` implies `X_n>0`. If `τ=t≤n` but `X_n>0`, the post-`τ` random-walk increments must have positive total; by independence, the geometric tail bound above gives

```text
Pr(X_n>0,τ≤n)
 ≤ ∑_(t=0)^n Pr(τ=t) (2sqrt(2)/3)^(n-t)
 = O(n^(-1/2)),
```

using exactly the same split at `t=n/2`. Thus `Pr(τ>n)=Pr(X_n>0)+O(n^(-1/2))`, with a uniform error. Combine with the preceding display and `X_n=a+2K_n-n` to prove the theorem. Berry–Esseen gives the final Gaussian approximation with standard deviation `(2sqrt(2)/3)*sqrt(n)`. No assumption of stochasticity in the authentic blank-origin orbit is made.

## Independent finite sanity checks

The integer recurrence in [verify_counts.py](verify_counts.py) gives, for example:

| n | a | Exact p_a(n) | Binomial endpoint probability |
| ---: | ---: | ---: | ---: |
| 30 | 10 | 0.510873 | 0.415240 |
| 60 | 20 | 0.504228 | 0.439686 |
| 100 | 33 | 0.500567 | 0.481197 |
| 200 | 67 | 0.519748 | 0.506638 |
| 300 | 100 | 0.500185 | 0.472890 |

The oscillating finite discrepancy includes the lattice parity/continuity correction; its decay with `n` is controlled uniformly by the proof, while the normal approximation centers at one half along `a≈n/3`.

## Scope and mathematical significance

This theorem gives an exact *population-law* for the source B-drain whose error holds **for every first counter**, including the moving transition regime `a∼n/3`. It places the preceding exponential phase transition and algebraic fixed-a asymptotics into one quantitative framework. It does **not** say that the actual high-level orbit ever visits a random-looking B-input or that the orbit cannot lie in a rare failure set. The central BB(6) objective still requires a genuine blank-root invariant or finite halting witness. All assertions in this note are paper derivations from a pinned source-verified recurrence; formalization of the probabilistic coupling is separate future work.
