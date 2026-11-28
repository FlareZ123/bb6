# F321: a density-7/10 infinite exclusion of terminal counter parameters

**Theorem (paper proof; 28 November 2026).** Consider the source-formalized two-counter return map of the F321 Busy Beaver holdout
`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`, started at `(a,d)=(1,1)`. Its only halting counter gate is `H_d=(d+1,d)`. There is an explicit, decidable subset `E ⊆ ℕ` of **natural density exactly 7/10** such that `H_d` is *not reachable* from the authentic seed for every `d∈E`. In fact, each such `H_d` has a finite inverse ancestry that ends in an impossible (zero-predecessor) counter pair, without encountering the seed.

This is an unbounded mathematical exclusion, not a bounded forward simulation or a theorem of global nonhalting. **Proof status:** elementary proof below for the counter map given by [the upstream Lean reduction](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean). Our new exclusion proof is *not yet kernel-checked in Lean* nor consumed by an original-source six-state theorem. The upstream source has `HasCollatzReduction` and `IsValidAcceleration`, **not** an unconditional blank-root halt decision. This result does not establish an exact BB(6) value or close Raw132.

## 1. Source map and exact inverse rules

For nonnegative integers, the upstream return map is
```
T(a,d) =
    (a-d-2, 2d+3)        if a ≥ d+2
    HALT                 if a = d+1
    (2a+4, 1)            if a = d
    (4a+6, d-3a)         if a < d and d ≥ 3a+1
    (4a+6, 2)            if a < d < 3a+1 and d-a is even
    (4a+6, 1)            if a < d < 3a+1 and d-a is odd.
```
The authentic counter seed is `(1,1)`; the upstream original-machine reduction records its entrance after 70 primitive transitions. To study a *fixed* nonhalting output `(A,D)`, solve these mutually exclusive branches backwards. The list of all possible predecessors is:

| Forward branch | Necessary/sufficient output condition | Unique or enumerated predecessor |
| --- | --- | --- |
| High | `D≥3` odd | `(A+(D−3)/2+2, (D−3)/2)` |
| Equality | `D=1, A≥4` even | `((A−4)/2, (A−4)/2)` |
| Far | `D≥1, A≥6, A≡2 (mod4)` | `((A−6)/4, D+3(A−6)/4)` |
| Middle | `D∈{1,2}, A≥10, A≡2 (mod4)` | all `((A−6)/4,d)` with `(A−6)/4<d≤3(A−6)/4` and parity `d−(A−6)/4 ≡ D−1 (mod2)` |

For the middle row, this parity condition is written so that `D=1` requires odd difference and `D=2` requires even difference. Every row follows by rearranging its branch equations and guard; conversely, substituting any listed antecedent into `T` reproduces `(A,D)`. We therefore have a **complete inverse map**, with no unspecified branch.

Two immediate consequences, used repeatedly: (i) any output with *even* `D` and `A ≢ 2 (mod4)` has **no predecessors**; (ii) any output with `D≥3` even and `A≡2 (mod4)` has exactly one predecessor, the far one; any output with `D≥3` odd and `A` odd has exactly one predecessor, the high one.

## 2. Explicit density-7/10 exclusion set

Define `E` as a disjoint union of the following classes:

1. Every **even** terminal parameter `d`.
2. Every `d≡7 (mod8)`.
3. For each integer `t≥0`, the progression
   ```
   d ≡ (16·4^t − 7)/3    (mod 32·4^t).            [zero]
   ```
4. For each **even** integer `t≥0`, the progression
   ```
   d ≡ (88·4^t − 7)/3    (mod 32·4^t).            [three]
   ```

The displayed residues are integers because `4^t≡1 (mod3)`. Initial progressions are:

| Class | Initial terminal residues |
| --- | --- |
| Even | `0,2,4,…` |
| 7 modulo 8 | `7 (mod8)` |
| [zero] | `3 (mod32)`, `19 (mod128)`, `83 (mod512)`, `339 (mod2048)`, … |
| [three], even t | `27 (mod32)`, `467 (mod512)`, `7507 (mod8192)`, … |

To see the disjointness, restrict to `d≡3 (mod8)` for the last two families and write `k=(d−3)/8). In base four, the low-order digits of `k` are `t` consecutive 2s followed by digit **0** in [zero], or `t` consecutive 2s followed by digit **3** in [three], with `t` even for the latter. These are mutually exclusive, and neither meets the even or 7-modulo-8 classes.

## 3. Proof of all-time exclusion

**Even d.** The gate is `H_d=(d+1,d)`, with odd first coordinate and even second coordinate. It has no predecessors by the inverse list; it is not the seed `(1,1)`.

**d≡7 (mod8).** Write `d=8k+7`. Its gate has a **unique** high predecessor
```
H_d ← (12k+12, 4k+2).
```
The displayed predecessor has `D` even and `A≡0 (mod4)`, so has no predecessors. Neither pair is the seed.

**d≡3 (mod8): common inverse reduction.** Write `d=8k+3`, `k≥0`. The gate first has the unique high predecessor
```
H_d ← (12k+6, 4k).
```
If `k=0`, this last pair has `D=0` and no antecedents. For `k≥1`, its unique far predecessor is `Q_0=(3k,13k)`. More generally define
```
c_i = 4^(i+2)−3,       b_i = 32(4^i−1)/3 − 6i,
Q_i(k) = (3k, c_i k+b_i).
```
Thus `c_0=13,b_0=0`. If `k_i=4k_(i+1)+2`, the point `Q_i(k_i)` has **exactly one** predecessor, the far one:
```
Q_i(k_i) ← Q_(i+1)(k_(i+1)),
c_(i+1)=4c_i+9,   b_(i+1)=b_i+2c_i.
```
Indeed `k_i≡2 (mod4)` makes `3k_i≡2 (mod4)`; its right coordinate is even and at least 26, hence only the far inverse applies. Substitution gives the displayed recursion. The formulas imply for all `i≥0`:
```
c_i ≡1 (mod4),  c_i≡5 (mod8),  b_i≡2i (mod8).
```

For the [zero] family, base-four decomposition means `k_0=2(4^t−1)/3+4^t k_t` with `k_t≡0 (mod4)`. Apply the unique predecessor recursion exactly `t` times (with the already-handled `k_0=0` exception). At `Q_t(k_t)`, the first coordinate `3k_t` is `0 mod4` and the second `c_t k_t+b_t` is even. Thus **there is no predecessor**. Every pair on this chain differs from the seed, so `H_d` is unreachable.

For the [three] family, the same `t)-fold recursion yields `k_t≡3 (mod4)` with **t even**. At `Q_t(k_t)=(A,D)`, `A` is odd and `D≡c_t·3+b_t≡3 (mod4)` (because `c_t≡1 (mod4)` and even `t` gives `b_t≡0 (mod4)`). Hence `Q_t` has exactly one high predecessor `R`:
```
R = (A+(D−3)/2+2, (D−3)/2).
```
Its second coordinate is even and its first coordinate is odd; by the inverse list, **R has no predecessors**. Again the finite ancestral chain misses the seed, proving exclusion.

This proves the theorem for **every** index in all four infinite families, not just checked small parameters.

## 4. Natural density

For each finite collection of arithmetic progressions, densities add because the four families are disjoint. The limiting densities of the two infinite families are
```
[zero]  Σ_(t≥0) 1/(32·4^t)  = 1/24,
[three] Σ_(n≥0) 1/(32·4^(2n)) = 1/30.
```
The tails are controlled uniformly by containing all as-yet uncounted base-four suffixes within a single progression whose modulus grows with the truncation, so they have upper natural density tending to zero. Therefore the infinite union has a genuine natural density and
```
dens(E) = 1/2 + 1/8 + 1/24 + 1/30 = 7/10.
```
The complement still has density **3/10** and contains infinitely many candidate halting parameters. The theorem cannot be promoted to a full F321 decision.

## 5. Reproduction, scope and next proof edge

The original-source counter map and its complete inverse are independently encoded in [the reproducible exact inverse-sieve script](../im-results/agent31-f321-bulk/f321-inverse-sieve.cjs); run `node im-results/agent31-f321-bulk/f321-inverse-sieve.cjs 30000`. It tests the forward/inverse rules on all 4,900 small ordered pairs and checks that every classified gate `0≤d<30000` has a unique chain to a zero-indegree pair without hitting `(1,1)`. The bounded regression covers **21,001** such `d` (70.003%; the extra one is a finite boundary effect). The script is *not* the reason the infinite theorem holds: the induction in §3 supplies that proof.

The related [dual logarithmic forward accelerators, complete maximal-block inverse and root experiment](../im-results/agent31-f321-bulk/README.md) provide a second entry point. The source-faithful next proof question is to construct new, complete inverse ancestry obstructions for a positive fraction of the remaining `3/10` of terminal rays, or prove nonattainment for **all** terminal parameters. A source-connected Lean formalization of §1–4 would then let this result join the upstream original-machine reduction. Neither this article nor the accepted F197 cylinder discharges the much larger Raw132 parent Cover.
