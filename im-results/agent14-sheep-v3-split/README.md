# A complete 3-adic root sieve for the previously unclassified Sheep power residues

**Agent 14, 9 November 2026. Research status: exact-integer all-parameter mathematical certificate, derived from the genuine original-source first-even transition equation.** The joint original-machine Lean theorem has not yet been built for this new family; the result is held in `im-results/` pending source import and priority review. The Sheep machine's actual blank-start halting status and BB(6) remain unknown.

## Main theorem and scope

Let `E` be the genuine even-first-return graph for the Sheep machine
`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, constructed in the pinned original Cryptids source and bridged by Agent 16's original-machine theorem. Write `y = 2^(17496*n)`.

**Theorem (paper proof plus complete-period exact-integer certificate).** For every integer `n >= 1` with `3 ∤ n`, every *even* source of an `E` edge into `y` must have hidden odd-return valuation `h` and two-adic source valuation `a` satisfying one of these two necessary alternatives:

1. `(h,a) = (3,6)`, possible under the generic inverse congruence only when `n ≡ 1 (mod 7)`;
2. `(h,a) = (8,2)`, possible under the generic inverse congruence only when `n ≡ 8 (mod 9)`.

The exceptional odd-cofactor-three source is impossible for all these targets. Therefore, if `3 ∤ n`, `n % 7 != 1`, and `n % 9 != 8`, the target `2^(17496*n)` has no incoming even-return edge, and is unreachable from the genuine blank first-even seed `10`.

This gives **30 new complete infinite residue classes `n=r+63k`**, with any `k≥0` and

```
r = 2,4,5,7,10,11,13,14,16,19,20,23,25,28,31,
    32,34,37,38,40,41,46,47,49,52,55,56,58,59,61
```

or, equivalently, 30 complete exponent classes `j=17496*r+1102248*k`. They are contained within the **seven** `j`-mod-122472 classes that the prior [222-family certificate](../agent14-sheep-inverse-dag-222/README.md) deliberately left out because a bound on hidden `h` was not uniform along the full old progression. These new classes are disjoint from that prior 222-class set. The new exponent density is exactly `30/1102248`, with no inference about halting probabilities.

## Proof reduction

**1. Uniform 3-adic cutoff.** Since `17496 = 8*3^7`, the standard lifting-the-exponent identity gives, for `3 ∤ n`,

```
v3(2^(17496*n) - 1)
 = v3(4 - 1) + v3(17496*n/2)
 = 1 + 7 = 8.
```

In the exact even-return inverse formula a target has the form `y=1+3^h*u` with odd positive `u`. Hence necessarily `0 ≤ h ≤ 8`. The cutoff is uniform for all `n=r+63k` with `3 ∤ r`.

**2. Generic inverse congruences.** The original source inverse splitter `SheepEvenSourceAlgebra.original_even_edge_inverse_cases` says that a generic source `x=2^a*v` (`a≥1`, odd `v≥5`) must satisfy

```
3^h*(2^(a+1)+1)*v + 2*a*3^h + 2^(h+1)
 = 2^(17496*n+h+1) + 3^(h+1).
```

Thus, with `D=3^h`, `M=D*(2^(a+1)+1)`, and `K=D*(2*a-3)+2^(h+1)`,

```
2^(17496*n+h+1) ≡ K (mod M).
```

For each of the nine `h` values, find the least `A_h` with `1<K(A_h)<2^A_h` and `2^A_h≥2D`. Because `K(a+1)=K(a)+2D`, the gap persists for every `a≥A_h`. Each `K(a)` is odd. The independently existing Lean theorem [`SheepOddGap.no_power_signed_small_odd`](../agent14-sheep-even-inverse/SheepOddGap.lean) excludes a power of two congruent to `K(a)` modulo `2^(a+1)+1`. Every `M` is divisible by this modulus, so **all high `a` are impossible**.

There are exactly **87 remaining low-`a` pairs**. Let `L=17496*63=1102248`. For each pair, the verifier computes a finite `q≤17` satisfying `2^(L*q) ≡ 1 (mod M)`, and checks every `t=0..q-1` for the congruence at `n=r+63t`. This is exhaustive for *all* `k`, by the displayed proven period. Over all 42 `r` with `1≤r≤63, 3 ∤ r`, only `(h,a)=(3,6)` remains when `r≡1 mod7`, and only `(h,a)=(8,2)` remains when `r≡8 mod9`. Every other row fails its entire period.

**3. Exceptional branch.** For a source with odd cofactor exactly three, the original source splitter gives

```
3^h*(3*2^a+a+2) + 2^h = 2^(17496*n+h).
```

Write the left side as `3^(h+1)*2^a + R(a)`, with `R(a)=3^h*(a+2)+2^h`. For `a≥30` and `h≤8`, exact base inequalities `0<R(30)<2^30` propagate to all larger `a`; therefore this integer lies strictly between `3^(h+1)*2^a` and `(3^(h+1)+1)*2^a`. No power of two lies in this interval because `3^(h+1)` is an integer immediately below the next potential power-of-two integer boundary, and `3^(h+1)` itself is not a power of two. For `a≤29`, the entire left side is below `2^44` (the largest such value occurs at `h=8,a=29`); meanwhile the right side is at least `2^17496`. Thus every exceptional case is impossible.

**4. Root reachability.** The target is larger than `10`, so any finite path from `10` to it has a last even-return edge. The predecessor exclusions forbid that edge, with no simulation-time restriction. This use of the genuine section is covered by the prior first-even source bridge; the new all-index modular arithmetic is independently certified below.

## Reproduce

Run [`certificate.py`](./certificate.py) with Python 3.10+ and the standard library. It prints the 30 classes after recomputing all 87 complete modular periods, 42 root residue censuses, all special base inequalities, and all low/high thresholds. Each computation is exact integer arithmetic. The period checks ensure the proof is uniform in `k`, rather than a sampled simulation. The checker deliberately keeps the modular residue candidates `(3,6)` and `(8,2)` as **necessary** only: it does not assume a modular solution is a genuine source edge.

**Open formalization:** lift the LTE valuation lemma, all 87 bounded modular exclusions and the exceptional gap into a single Lean `∀k, ¬ SheepEven.EvenReach 10 (2^(17496*(r+63*k)))` theorem imported against unchanged original-machine source. The already proved `SheepOddGap` and `SheepEvenSourceAlgebra` are reusable. The existing 31104 inverse chain takes a separate path and is not a prerequisite for this theorem. This result excludes a positive arithmetic family of halting targets and leaves all other exponents and full Sheep nonhalting unresolved.
