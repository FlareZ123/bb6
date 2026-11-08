# #623: exact drain-success counts and exponential scarcity

**Mathematical status (8 November 2026).** An exact all-input, all-length counting recurrence is derived below for the original Cryptids #623 complete B-drain, together with an explicit exponential upper bound. These are **paper proofs from an already source-certified exact recurrence**, checked independently by [`verify_counts.py`](verify_counts.py). The new cardinality and exponential estimates have **not separately been kernel formalized**. They describe enumeration of synthetic `B(a,b,d)` inputs, and establish **no** nonhalting or halting result for the true `D(0,7)` blank-root orbit, nor a BB(6) bound. They are intermediate research and belong in `im-results/`.

## Exact source interface

Use Agent 49's [source-pinned complete one-level recursion](../agent49-parity623/FlatDrainSource.lean) and [source synthesis](../agent49-parity623/FlatDrain.md). The original machine is `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, originally formalized in `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b`. The theorem `flatB_eq_drainB` proves equality of the entire recursive outputs on all natural inputs. Earlier Agent 8 [third-counter equivariance](../agent8-623-inverse/ThirdCounterAffineSource.lean) shows that the full drain's success/failure status is independent of `d`.

Define `f_a(b)=1` if `drainB a b d` succeeds and `f_a(b)=0` if it fails. It is well defined independently of `d`, and the exact source theorem gives, for all `q>=0`:

| Input | Exact success indicator |
| --- | --- |
| `b=0` | `f_a(0)=1` |
| `b=3q, q>0` | `f_a(3q)=f_{a+1}(q-1)` |
| `b=3q+1, a>0` | `f_a(3q+1)=f_{a-1}(q)` |
| `b=3q+1, a=0` | `f_0(3q+1)=0` |
| `b=3q+2, a>0` | `f_a(3q+2)=f_{a-1}(q+1)` |
| `b=3q+2, a=0` | `f_0(3q+2)=f_0(q)` |

The residual block count strictly decreases in every positive-input case. In particular the source has no failure mode omitted from the table.

## Theorem 1: exact counts for every ternary input length

For every `a,n ∈ ℕ`, define

```text
S_a(n) = # { b ∈ ℕ : 0 ≤ b < 3^n and drainB(a,b,d) succeeds }.
```

The complete infinite family of exact recurrences is

```text
S_a(0) = 1                                      (all a)
S_0(n) = S_0(n-1) + S_1(n-1) + [n even]         (n ≥ 1)
S_1(n) = 2 S_0(n-1) + S_2(n-1) - [n odd]      (n ≥ 1)
S_a(n) = 2 S_(a-1)(n-1) + S_(a+1)(n-1)         (n ≥ 1, a ≥ 2).
```

Here `[P]` denotes 1 if P and 0 otherwise. This determines all `S_a(n)` by finite integer arithmetic. In particular, a table for all `a≤A` and `n≤N` requires only `O(N(A+N))` integer additions and `O(A+N)` integer storage, plus big-integer cost. The upper counter boundary can be set beyond `A+N` because the recurrence moves `a` at most one per stage.

**Proof of the exceptional terms.** The exact source cases imply, for every `k≥0`,

```text
f_a(3^k)   = 1 if (k odd or a>0); otherwise 0,
f_a(3^k-1) = 0 exactly if (a=1 and k odd); otherwise 1.
```

For the first identity, `f_a(1)=[a>0]`, `f_a(3)=1`, and for `k≥2`, the `3q` and `3q+2` rules give `f_a(3^k)=f_a(3^(k-2))`. For the second, `f_0(3^k-1)=1` follows by repeatedly applying the `a=0,3q+2` rule, while `f_a(3^k-1)=f_{a-1}(3^(k-1))` when `a>0,k≥1`.

For `n≥1`, set `m=3^(n-1)`. The complete input interval `[0,3m)` partitions into `b=0`, positive multiples `3q` for `1≤q<m`, and `3q+1`, `3q+2` for `0≤q<m`. Therefore for `a≥1`,

```text
S_a(n)
 = S_(a+1)(n-1) + 2 S_(a-1)(n-1)
   - f_(a+1)(m-1) + f_(a-1)(m).
```

Since `a+1≥2`, the first boundary indicator equals 1. The other equals 1 for all `a≥2`, and equals `[n even]` for `a=1`. This proves the last two recurrences. When `a=0`, the `3q+1` branch always fails and the `3q+2` branch is `f_0(q)`, so

```text
S_0(n)=1+S_1(n-1)-f_1(m-1)+S_0(n-1),
```

where `f_1(m-1)=[n odd]`. This proves the remaining recurrence. All identities are exact for **every** finite `n` and `a`.

## Theorem 2: an explicit exponential density bound

For all `a,n∈ℕ`,

```text
S_a(n) ≤ 3 (3/2)^a (17/6)^n.
S_a(n)/3^n ≤ 3 (3/2)^a (17/18)^n.
```

**Proof.** Put `r=3/2` and `λ=r+2/r=17/6`. Induct on `n`, simultaneously for every `a`. At `n=0`, `S_a(0)=1≤3r^a`. For `a≥1`, drop the nonpositive odd-parity correction when necessary, and apply the induction bounds to obtain

```text
S_a(n) ≤ 3 λ^(n-1) (r^(a+1)+2r^(a-1))
       = 3 r^a λ^n.
```

For `a=0`, use `[n even]≤1`:

```text
S_0(n) ≤ 3 λ^(n-1)(1+r)+1
       ≤ 3 λ^(n-1)(1+r+(λ-1-r))
       = 3 λ^n.
```

The middle inequality follows from `3 λ^(n-1)(λ-1-r)=λ^(n-1)≥1`, because `λ-1-r=1/3` and `n≥1`. Division by `3^n` proves the second bound.

**Sharper rate.** The identical induction works for any `1<r<2` with `λ=r+2/r` and prefactor `r/(2-r)`, because `λ-1-r=2/r-1`. Taking `r=√2` minimizes `λ`, giving the paper theorem

```text
S_a(n) ≤ (1+√2) (√2)^a (2√2)^n,
S_a(n)/3^n ≤ (1+√2) (√2)^a (2√2/3)^n.
```

Thus the relative density of successful complete drains tends to **zero exponentially** for each fixed first counter `a`, even though both the successful and failed input sets are infinite. More generally the displayed bound still decays along any sequence `a(n)=o(n)`. For `a(n)` proportional to `n`, choosing `r` sufficiently near 1 gives exponential decay when `limsup a(n)/n<1/3`. The count is an enumeration over the freely chosen B-block input `b`; it is not a frequency statement about the unique deterministic blank-root orbit.

## Reproducible check and exact values

[`verify_counts.py`](verify_counts.py) contains an independently implemented complete one-level drain predicate, an `O(N²)` exact recurrence generator, assertions of direct equality for all `a=0..11` and `n=0..9`, and rational comparisons with the `17/6` bound for `a=0..15,n=0..150`. No random sampling or libraries beyond Python's standard library are involved. A local independent implementation was already compared with brute enumeration for `n≤8`; the durable script extends this regression to `n=9`.

For illustration, the exact `S_0(n)` sequence at `n=0..12` is

```text
1, 2, 5, 12, 29, 76, 189, 508, 1293, 3508, 9069, 24732, 64637.
```

The corresponding exact `S_1(n)` sequence is

```text
1, 2, 7, 16, 47, 112, 319, 784, 2215, 5560, 15663, 39904, 112279.
```

These two infinite sequences are new concrete consequences of the source-complete recurrence. Their recurrence, rather than the finite listed values, establishes the result.

## Additional exact analytic consequences

The source-derived recurrence has further exact mathematical consequences, documented separately to keep this entry point concise:

- [AlgebraicGF.md](AlgebraicGF.md) derives an algebraic ordinary generating function for `S_0(n)` and the sharp two-parity asymptotic `S_0(n)≈C_(n mod 2)(2√2)^n/n^(3/2)`.
- [PhaseTransition.md](PhaseTransition.md) proves a density transition: for `a_n/n→α<1/3`, success density tends to zero exponentially, while for `α>1/3` it tends to one exponentially.
- [BinomialApproximation.md](BinomialApproximation.md) proves the uniform approximation `S_a(n)/3^n = P(a+2K_n-n>0)+O(n^(-1/2))` for `K_n∼Bin(n,1/3)`, with an absolute error constant independent of `a`. This yields the Gaussian profile `Φ(3x/(2√2))` in the critical window `a=n/3+x√n+o(√n)`.

The three extensions are paper proofs from the same original-source-certified drain recurrence, with finite computational cross-checks. They have not separately been Lean-kernel checked, and none gives a statement about the unique blank-root orbit.

## Scope, prior work and next root-sensitive test

Agent 49 had already source-certified the complete ternary recursion, failure bijection for `b<3^a`, and sharp matching-parity safety threshold; those discoveries are prior work and are not claimed here. The new contribution is the **all-length success cardinality recurrence** and the resulting **uniform exponential scarcity theorem**, which are not inferred from a finite cutoff. This is a mathematical derivation with source-certified premises and finite regression; its new quantifiers have yet to be formalized as a Lean counting theorem. Before external publication, compare with prior literature on deterministic ternary transducers/weighted lattice paths.

For real #623, the actual accelerated trajectory starts at `D(0,7)` and uses `highLevelNext` to generate individual `B(a,b,d)` inputs. Those deterministic inputs may occupy exceptional exponentially sparse sets, so the density theorem **cannot prove** the real machine halts or runs forever. A useful next step is to derive a **genuine blank-root restriction** on the ratio of the generated first counter to the logarithmic input length, or connect this exact count recurrence to a source-level inverse exclusion of an actual terminal family. Such a bridge would turn global synthetic counting into progress on a specific remaining BB(6) root.
