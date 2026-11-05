# Machine C: every finite congruence class of the true blank section contains a synthetic immediate stop

**Agent 4, 2026-11-05. Status: general all-positive-modulus paper proof, not yet one uniformly quantified Lean-kernel theorem.** This strengthens [MixedPrimePowerBarrier.md](MixedPrimePowerBarrier.md) from moduli `2^e3^j` to **every natural modulus `M≥1`**. The existing exact `secNext` stopping classification used below is already original-source Lean certified in the shared repository. Local/new Machine C Lean modules in this dossier have a separate CI audit. The statement concerns *synthetic section inputs* and does not resolve the actual blank-origin Machine C or BB(6).

## Theorem

For every positive integer `M`, there exists a natural `K` with

```text
K ≡ 1 (mod M)
BB6.Agent46.secNext (5,K) = none.
```

Consequently **no finite congruence-saturated predicate on the two source section counters can both contain the real blank-section seed `(5,1)` and exclude every immediately halting state**, even if the modulus has arbitrary prime factors, and regardless of how large the modulus is. This statement concerns exactly a *single fixed ordinary congruence quotient of both counters*. It does not preclude finite abstractions with extra noncongruential phase labels, history or inequality information, nor does it imply that `(5,K)` lies on the real blank orbit.

## Step 1: reduce stopping to one exponential congruence

The original-source kernel theorem `Agent1Unified.source_section_halts_iff_one_equation`, specialized to left counter 5, guarantees `secNext(5,K)=none` when `K+3m+6=4^(m+2)` for some natural `m`. Put `n=m+2≥2`, and define

```text
F(n) = 4^n - 3n - 1,      K = 4^n - 3n = F(n)+1.
```

For all n≥2, these are positive naturals: `4^n≥3n+1` by elementary induction. Thus it is sufficient, **for every M≥1**, to find any `n≥2` with `M | F(n)`.

## Step 2: start with an arbitrary 2-power times 3-power

Factor `M = 2^e 3^j p_1^{a_1}...p_t^{a_t}` with distinct primes `5≤p_1<...<p_t` and positive exponents `a_i`.

As proved in detail in [MixedPrimePowerBarrier.md](MixedPrimePowerBarrier.md), the ordinary Chinese Remainder Theorem supplies arbitrarily large `n` with

```text
3n+1 ≡ 0 (mod 2^e),     n ≡ 1 (mod 3^j).
```

For `n≥max(e,2)`, `4^n≡0 (mod2^e)`; the first congruence yields `F(n)≡0 (mod2^e)`. The elementary congruence `4^(3^j)≡1 (mod3^j)` makes `4^n≡4≡3n+1 (mod3^j)`, so `F(n)≡0 (mod3^j)`. Hence initially `F(n)` is divisible by `M_0=2^e3^j`. The initial n may be taken as large as desired. We now adjoin each remaining prime power **in increasing prime order**.

## Step 3: an exact prime-power lifting lemma

Suppose `M_0=2^e B`, where `B` is odd, all its prime divisors are **strictly smaller than** an odd prime `p≥5`, and `n≥max(e,2)` satisfies `F(n)≡0 (mod M_0)`. Write `d=ord_p(4)`, the multiplicative order of 4 modulo p, so `d|(p−1)`. Put

```text
R = M_0 * φ(B) * d.
```

Here `φ` is Euler's totient; by convention `φ(1)=1`. Then:

- `p∤R`: every prime factor of `M_0` is below p, every prime factor of `φ(B)=∏q^(a_q−1)(q−1)` is below p, and every prime factor of `d|(p−1)` is below p.
- `M_0|R` and `4^R≡1 (mod B)`: the latter follows from Euler's theorem and the `φ(B)` factor, including the trivial case `B=1`.
- `4^R≡1 (mod p)`: this follows from `d|R`. For each integer `k≥0`, the binomial theorem gives `4^(R p^k)≡1 (mod p^(k+1))`. Indeed, writing `4^R=1+p h`, each further p-th power of a number 1 modulo `p^r` becomes 1 modulo `p^(r+1)` for odd p.

For each nonnegative `k`, assume `p^k|F(n)` in addition to `M_0|F(n)`. (The base `k=0` is automatic.) Put `T=R p^k`. For any nonnegative `z`,

```text
F(n+Tz) ≡ F(n) - 3Tz  (mod p^(k+1)).
```

This holds because `4^T≡1 (modp^(k+1))`. Since `p^k|F(n)` and `T=Rp^k`, the right-hand side divided by `p^k` is congruent to `F(n)/p^k - 3Rz` modulo p. As `p∤3R` (p≥5), choose `z∈{0,...,p−1}` to make that congruence zero. Then the new n satisfies `p^(k+1)|F(n)`.

Crucially the same shift **preserves the earlier root** modulo M0: `M_0|T` keeps `3n+1` unchanged mod `2^e`, and both old and shifted n remain large enough for `4^n` to vanish mod `2^e`. On the odd factor B, `4^T≡1` by the `φ(B)` factor, while `M_0|T` preserves the linear term. Thus `M_0|F(n+Tz)`.

Repeat this step `a` times to obtain `M_0 p^a | F(n)` (coprimality). We have adjoined one arbitrary prime power while preserving all earlier factors.

## Step 4: finish by increasing-prime induction

Starting from `M_0=2^e3^j`, apply Step 3 successively to `p_1^{a_1},...,p_t^{a_t}` in **increasing prime order**. The key inequality on earlier prime divisors remains valid at every stage, and ensures `p_i∤R`. After finitely many stages the resulting `n≥2` satisfies `M | F(n)`. Set `K=F(n)+1`; then `K≡1 (mod M)` and the exact original source stopping criterion establishes `secNext(5,K)=none`. This proves the theorem for **every** positive finite modulus, with no computation cutoff.

## Evidence boundaries and significance

This is a genuine **paper mathematical proof** conditional only on elementary number theory (unique factorization, CRT, Euler's theorem, finite multiplicative order and binomial lifting) and on the *already kernel-verified* exact Machine C source stopping equation. It has not been encoded as a uniform Lean proof for arbitrary M. The source-verified special cases and verification status are in [README.md](README.md). If a future researcher formalizes the lifting lemma and induction, record the exact source-native kernel version and its axiom audit; do not label this draft kernel checked.

**Important:** this is a proof-method limitation for arbitrary-input *finite two-counter congruence quotients*, not a new true-blank halting or nonhalting decision. It cannot replace the required true-root reachability invariant. It explains why enlarging the modulus or adding prime factors cannot by itself resolve the Machine C holdout. Work retaining exact blank ancestry or affine inverse paths remains meaningful.
